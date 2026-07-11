#!/usr/bin/env python3
"""Run a ZenoLedger v0 follower/watcher node.

The v0 node wraps the existing deterministic public-testnet bundle and watcher
primitives. It can bootstrap a bundle, replay it as an independent operator,
emit a watcher attestation, and serve the resulting node status over HTTP.
"""

from __future__ import annotations

import argparse
import fcntl
import hmac
import hashlib
import json
import os
import shutil
import tarfile
from collections import OrderedDict
from contextlib import contextmanager
import socket
import sys
import tempfile
import threading
import time
from http import HTTPStatus
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any, Mapping, NoReturn
from urllib.error import HTTPError
from urllib.parse import parse_qs, unquote, urljoin, urlparse
from urllib.request import HTTPRedirectHandler, Request, build_opener, urlopen

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.zeno_ledger_mirror import validate_mirror_index_v0
from src.integration.zeno_ledger_v0 import (
    BATCH_CUTOFF_SCHEMA_V0,
    BODY_SCHEMA_V0,
    INGRESS_RECEIPT_SCHEMA_V0,
    _normalize_dex_operations_for_apply_v0,
    build_checkpoint_v0,
    build_header_v0,
    build_tx_receipt_v0,
    canonical_body_root_v0,
    canonical_header_hash_v0,
    compute_app_hash_v0,
    compute_evidence_root_v0,
    compute_ingress_root_v0,
    compute_tx_root_v0,
    dex_state_root_v0,
    hash_v0,
    tx_hash_v0,
    validate_body_v0,
)
from src.integration.dex_snapshot import snapshot_from_state, state_from_snapshot
from src.integration.zeno_ledger_rejections_v0 import (
    BAD_AUTH,
    BAD_JSON,
    HTTP_POST_TOO_LARGE,
    build_rejection_report_v0,
)
from src.integration.zeno_ledger_production_key_gates_v0 import (
    validate_public_network_config_update_gate_v0,
)
from src.integration.zeno_ledger_signer_registry import verify_signature_quorum_v0
from src.integration.zeno_ledger_tokenomics import (
    LOCAL_TESTNET_BUYBACK_SHARE_BPS,
    LOCAL_TESTNET_BUYBACK_SOURCE_ALLOCATION_ID,
    MAX_LOCAL_TESTNET_ACTIVE_PARTICIPANT_CLAIM_AMOUNT,
    active_participant_program_by_id_v0,
    active_participant_reward_claim_key_v0,
    build_active_participant_reward_claim_v0,
    build_tokenomics_buyback_burn_event_v0,
    protocol_token_distribution_hash_v0,
    validate_active_participant_reward_claim_v0,
    validate_protocol_token_distribution_v0,
    validate_tokenomics_buyback_burn_event_v0,
)
from src.core.amm_dispatch import swap_exact_in_for_pool
from src.core.dex import DexConfig
from src.integration.dex_engine import DexEngineConfig, apply_ops
from src.state.balances import NATIVE_ASSET
from src.state.canonical import canonical_hex_fixed_allow_0x, canonical_json_bytes
from src.state.pools import compute_pool_id
from tools.zeno_ledger_make_public_testnet_bundle import build_public_testnet_bundle_v0
from tools.zeno_ledger_make_testnet_bundle import (
    DEFAULT_CHAIN_ID,
    DEFAULT_SEQUENCER_ID,
    DEFAULT_TIME_MS,
)
from tools.zeno_ledger_operator_rehearsal import run_operator_rehearsal_v0
from tools.zeno_ledger_run_local import ZERO_ROOT, build_local_block_v0
from tools.zeno_log_redaction import json_dumps_for_log


NODE_STATUS_SCHEMA = "zenodex.zeno_ledger.node_status.v0"
NODE_REPORT_SCHEMA = "zenodex.zeno_ledger.node_report.v0"
NODE_SYNC_REPORT_SCHEMA = "zenodex.zeno_ledger.node_sync_report.v0"
NODE_APPEND_REPORT_SCHEMA = "zenodex.zeno_ledger.node_append_report.v0"
NODE_PULL_REPORT_SCHEMA = "zenodex.zeno_ledger.node_pull_report.v0"
NODE_LIVE_STATE_SCHEMA = "zenodex.zeno_ledger.node_live_state.v0"
NODE_JOIN_CONFIG_SCHEMA = "zenodex.zeno_ledger.node_join_config.v0"
NODE_JOIN_REPORT_SCHEMA = "zenodex.zeno_ledger.node_join_report.v0"
NODE_PREFLIGHT_REPORT_SCHEMA = "zenodex.zeno_ledger.node_preflight_report.v0"
NODE_PEER_CHECK_REPORT_SCHEMA = "zenodex.zeno_ledger.node_peer_check_report.v0"
NODE_PUBLIC_NETWORK_CONFIG_SCHEMA = "zenodex.zeno_ledger.public_network_config.v0"
MAX_REMOTE_ARTIFACT_BYTES = 16 * 1024 * 1024
MAX_REMOTE_BUNDLE_ARCHIVE_BYTES = 64 * 1024 * 1024
MAX_HTTP_POST_BYTES = 2 * 1024 * 1024
MAX_TESTNET_FAUCET_AMOUNT = 1_000_000_000_000
TESTNET_FAUCET_KIND = "ZENODEX_TESTNET_FAUCET"
TOKENOMICS_REWARD_CLAIM_KIND = "ZENODEX_ACTIVE_PARTICIPANT_REWARD_CLAIM"
TOKENOMICS_BUYBACK_BURN_OP_STREAM = "12"
TOKENOMICS_BUYBACK_BURN_OP_KIND = "ZENODEX_TOKENOMICS_BUYBACK_BURN"
PEER_FOLLOW_ERROR_LOG_CAP_PER_PEER = 64
PUBLIC_BUNDLE_ARCHIVE_NAME = "public_testnet_bundle.tar.gz"


def _write_stdout_json(value: Mapping[str, Any]) -> None:
    os.write(1, (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8"))


class _HttpRejectedError(ValueError):
    def __init__(self, *, status: HTTPStatus, report: Mapping[str, Any]) -> None:
        self.status = status
        self.report = dict(report)
        super().__init__(str(self.report.get("detail", "request rejected")))


class _TrustedLocalArtifactPath:
    """Marker for paths that have passed the caller's local-artifact boundary."""

    __slots__ = ("path",)

    def __init__(self, path: Path) -> None:
        self.path = path


def _trusted_local_artifact_path_v0(path: Path) -> _TrustedLocalArtifactPath:
    if not isinstance(path, Path):
        raise TypeError("artifact path must be a Path")
    return _TrustedLocalArtifactPath(path)


def _artifact_is_file_v0(path: Path) -> bool:
    trusted = _trusted_local_artifact_path_v0(path)
    return trusted.path.is_file()


def _read_artifact_text_v0(path: Path) -> str:
    trusted = _trusted_local_artifact_path_v0(path)
    return trusted.path.read_text(encoding="utf-8")


def _read_artifact_bytes_v0(path: Path) -> bytes:
    trusted = _trusted_local_artifact_path_v0(path)
    return trusted.path.read_bytes()


# Callers pass local operator/configured artifact paths, and HTTP-exposed paths
# have their own root containment checks.
def _load_json_object(path: Path) -> Mapping[str, Any]:
    obj = json.loads(_read_artifact_text_v0(path))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must decode to a JSON object")
    return obj


def _is_tau_app_state_obj_v0(obj: Mapping[str, Any]) -> bool:
    return obj.get("schema") == "zenodex/tau_app_state/v1" and isinstance(obj.get("dex_state"), Mapping)


def _dex_snapshot_from_state_file_obj_v0(obj: Mapping[str, Any]) -> Mapping[str, Any]:
    if _is_tau_app_state_obj_v0(obj):
        dex_state = obj.get("dex_state")
        if not isinstance(dex_state, Mapping):
            raise ValueError("app_state.dex_state must be an object")
        return dex_state
    return obj


def _state_root_for_live_state_file_v0(path: Path) -> str:
    obj = _load_json_object(path)
    return _state_root_for_state_file_obj_v0(obj)


def _state_root_for_state_file_obj_v0(obj: Mapping[str, Any]) -> str:
    if _is_tau_app_state_obj_v0(obj):
        digest = hashlib.sha256(canonical_json_bytes(dict(obj))).hexdigest()
        return canonical_hex_fixed_allow_0x(digest, nbytes=32, name="app_state_hash")
    return dex_state_root_v0(state_from_snapshot(obj))


def _replace_dex_snapshot_in_state_file_obj_v0(
    original: Mapping[str, Any],
    dex_snapshot: Mapping[str, Any],
) -> Mapping[str, Any]:
    if _is_tau_app_state_obj_v0(original):
        wrapped = dict(original)
        wrapped["dex_state"] = dict(dex_snapshot)
        return wrapped
    return dex_snapshot


def _native_chain_balances_from_snapshot_v0(snapshot: Mapping[str, Any]) -> dict[str, int]:
    state = state_from_snapshot(snapshot)
    out: dict[str, int] = {}
    for (pubkey, asset), amount in state.balances.get_all_balances().items():
        if asset == NATIVE_ASSET and int(amount) > 0:
            out[str(pubkey)] = int(amount)
    return out


def _write_json(path: Path, value: object) -> None:
    """Crash-safe single-file write: tmp + fsync + replace + dir fsync.

    A torn pointer (live_state.json) or accepted-then-overwritten artifact is
    the durability gap Bug 25 exposes. ``tempfile.mkstemp`` gives us a random
    tmp name in the same directory — no hijack by a pre-existing ``*.tmp``
    symlink and no collision between concurrent writers. The parent-directory
    fsync makes the rename itself survive a hard crash.
    """
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = json.dumps(value, indent=2, sort_keys=True) + "\n"
    fd, tmp_str = tempfile.mkstemp(prefix=path.name + ".", suffix=".tmp", dir=path.parent)
    tmp = Path(tmp_str)
    fh: Any = None
    try:
        fh = os.fdopen(fd, "w", encoding="utf-8")
    except Exception:
        try:
            os.close(fd)
        except OSError:
            pass
        try:
            tmp.unlink()
        except FileNotFoundError:
            pass
        raise
    try:
        with fh:
            fh.write(payload)
            fh.flush()
            os.fsync(fh.fileno())
        os.replace(tmp, path)
    except Exception:
        try:
            tmp.unlink()
        except FileNotFoundError:
            pass
        raise
    try:
        dir_fd = os.open(path.parent, os.O_RDONLY)
    except OSError:
        return
    try:
        os.fsync(dir_fd)
    finally:
        os.close(dir_fd)


def _raise_http_rejection(
    *,
    status: HTTPStatus,
    code: str,
    detail: str,
    **fields: object,
) -> NoReturn:
    raise _HttpRejectedError(
        status=status,
        report=build_rejection_report_v0(code, detail, error=detail, **fields),
    )


def _live_state_path_text_v0(*, data_dir: Path, path: str | Path, field: str) -> str:
    """Encode a live_state artifact path relative to data_dir.

    CLI callers may pass ``--data-dir`` as a relative path. Storing
    ``str(data_dir / "live_ledger" / ...)`` in live_state would then be
    interpreted as relative to data_dir again during restart validation. Keep
    live_state path fields data-dir-relative so they survive restarts from the
    same node directory regardless of whether the operator used an absolute or
    relative data_dir argument.
    """

    data_root = data_dir.resolve()
    resolved = Path(path).resolve()
    if resolved == data_root or data_root not in resolved.parents:
        raise ValueError(f"{field} must resolve to a path inside the node data_dir")
    return resolved.relative_to(data_root).as_posix()


def _is_safe_relative(path_text: str) -> bool:
    path = Path(path_text)
    return (
        path_text != ""
        and not path.is_absolute()
        and ".." not in path.parts
        and "://" not in path_text
        and "\\" not in path_text
    )


def _remote_url(base_url: str, rel_path: str) -> str:
    if not _is_http_url(base_url):
        raise ValueError("base_url must be an http(s) URL without embedded credentials")
    if not _is_safe_relative(rel_path):
        raise ValueError(f"unsafe remote path: {rel_path}")
    base = base_url.rstrip("/") + "/"
    return urljoin(base, rel_path)


def _fetch_remote_bytes(url: str, *, max_bytes: int = MAX_REMOTE_ARTIFACT_BYTES) -> bytes:
    with urlopen(url, timeout=30) as response:  # noqa: S310 - explicit user-supplied mirror URL
        length = response.headers.get("Content-Length")
        if length is not None:
            try:
                if int(length) > max_bytes:
                    raise ValueError(f"remote artifact too large: {url}")
            except ValueError:
                raise
        data = response.read(max_bytes + 1)
    if len(data) > max_bytes:
        raise ValueError(f"remote artifact too large: {url}")
    return data


def _write_remote_file(*, base_url: str, rel_path: str, out_root: Path) -> bytes:
    data = _fetch_remote_bytes(_remote_url(base_url, rel_path))
    out_path = out_root / rel_path
    _write_bytes_atomic(out_path, data)
    return data


def _write_bytes_atomic(path: Path, data: bytes) -> None:
    """Crash-safe bytes write: tmp + fsync + replace + dir fsync.

    Mirrors ``_write_json``'s durability guarantees for downloaded remote
    artifacts so a crash mid-sync cannot leave a partial file on disk.
    """
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp_str = tempfile.mkstemp(prefix=path.name + ".", suffix=".tmp", dir=path.parent)
    tmp = Path(tmp_str)
    fh: Any = None
    try:
        fh = os.fdopen(fd, "wb")
    except Exception:
        try:
            os.close(fd)
        except OSError:
            pass
        try:
            tmp.unlink()
        except FileNotFoundError:
            pass
        raise
    try:
        with fh:
            fh.write(data)
            fh.flush()
            os.fsync(fh.fileno())
        os.replace(tmp, path)
    except Exception:
        try:
            tmp.unlink()
        except FileNotFoundError:
            pass
        raise
    try:
        dir_fd = os.open(path.parent, os.O_RDONLY)
    except OSError:
        return
    try:
        os.fsync(dir_fd)
    finally:
        os.close(dir_fd)


def _download_json(*, base_url: str, rel_path: str, out_root: Path) -> dict[str, Any]:
    data = _write_remote_file(base_url=base_url, rel_path=rel_path, out_root=out_root)
    obj = json.loads(data.decode("utf-8"))
    if not isinstance(obj, dict):
        raise ValueError(f"{rel_path} must decode to a JSON object")
    return obj


def _fetch_json_url(url: str) -> dict[str, Any]:
    if not _is_http_url(url):
        raise ValueError("url must be an http(s) URL without embedded credentials")
    data = _fetch_remote_bytes(url)
    obj = json.loads(data.decode("utf-8"))
    if not isinstance(obj, dict):
        raise ValueError(f"{url} must decode to a JSON object")
    return obj


class _NoRedirectHandler(HTTPRedirectHandler):
    """Reject redirects so bearer credentials cannot be replayed to another URL."""

    def redirect_request(
        self,
        req: Request,
        fp: Any,
        code: int,
        msg: str,
        headers: Mapping[str, str],
        newurl: str,
    ) -> None:
        # DbC invariant: authenticated POSTs must either reach the configured URL
        # directly or fail closed; urllib must not clone Authorization onto a
        # redirected request.
        return None


_AUTHENTICATED_POST_OPENER = build_opener(_NoRedirectHandler)


def _auth_bearer_header(token: str | None) -> dict[str, str]:
    if token is None:
        return {}
    return {"Authorization": f"Bearer {token}"}


def _open_post_request_auth_safe(request: Request, *, bearer_token: str | None, timeout: int):
    # DbC precondition: callers pass the same bearer token used to build the
    # request headers, keeping redirect policy coupled to credential presence.
    if bearer_token is None:
        return urlopen(request, timeout=timeout)  # noqa: S310 - explicit operator-configured peer URL
    return _AUTHENTICATED_POST_OPENER.open(request, timeout=timeout)


def _auth_token_from_env_name(env_name: object, *, name: str) -> str | None:
    if env_name is None:
        return None
    if not isinstance(env_name, str) or env_name == "":
        raise ValueError(f"{name} must be a non-empty environment variable name")
    token = os.environ.get(env_name)
    if not token:
        raise ValueError(f"{name} points to an unset or empty environment variable")
    return token


def _auth_token_from_config(config: Mapping[str, Any], *, token_key: str, env_key: str) -> str | None:
    inline_token = config.get(token_key)
    env_name = config.get(env_key)
    if inline_token is not None and env_name is not None:
        raise ValueError(f"{token_key} and {env_key} must not both be set")
    if inline_token is not None:
        if not isinstance(inline_token, str) or inline_token == "":
            raise ValueError(f"{token_key} must be a non-empty string")
        return inline_token
    return _auth_token_from_env_name(env_name, name=env_key)


def _post_json_url(url: str, value: Mapping[str, Any], *, bearer_token: str | None = None) -> tuple[dict[str, Any], HTTPStatus]:
    if not _is_http_url(url):
        raise ValueError("url must be an http(s) URL without embedded credentials")
    payload = json.dumps(dict(value), sort_keys=True).encode("utf-8")
    request = Request(
        url,
        data=payload,
        headers={"Content-Type": "application/json", **_auth_bearer_header(bearer_token)},
        method="POST",
    )
    try:
        with _open_post_request_auth_safe(request, bearer_token=bearer_token, timeout=30) as response:
            status = HTTPStatus(response.status)
            data = response.read(MAX_REMOTE_ARTIFACT_BYTES + 1)
    except HTTPError as exc:
        status = HTTPStatus(exc.code)
        data = exc.read(MAX_REMOTE_ARTIFACT_BYTES + 1)
    if len(data) > MAX_REMOTE_ARTIFACT_BYTES:
        raise ValueError(f"remote response too large: {url}")
    obj = json.loads(data.decode("utf-8"))
    if not isinstance(obj, dict):
        raise ValueError(f"{url} must decode to a JSON object")
    return obj, status


def _sha256_bytes(data: bytes) -> str:
    return "0x" + hashlib.sha256(data).hexdigest()


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1024 * 1024), b""):
            h.update(chunk)
    return "0x" + h.hexdigest()


def _public_bundle_archive_path_v0(bundle_root: Path) -> Path:
    return bundle_root / PUBLIC_BUNDLE_ARCHIVE_NAME


def _is_relative_safe_archive_name_v0(name: str) -> bool:
    member_path = Path(name)
    return (
        name != ""
        and not member_path.is_absolute()
        and ".." not in member_path.parts
        and "://" not in name
        and "\\" not in name
    )


def _extract_public_bundle_archive_v0(*, archive_bytes: bytes, out_dir: Path) -> None:
    with tempfile.TemporaryDirectory(prefix="zeno-ledger-public-bundle-") as tmp:
        tmp_root = Path(tmp)
        archive_path = tmp_root / "bundle.tar.gz"
        archive_path.write_bytes(archive_bytes)
        extract_root = tmp_root / "extract"
        extract_root.mkdir()
        with tarfile.open(archive_path, "r:gz") as archive:
            members = archive.getmembers()
            if not members:
                raise ValueError("bundle archive is empty")
            for member in members:
                if not _is_relative_safe_archive_name_v0(member.name):
                    raise ValueError(f"unsafe bundle archive member: {member.name}")
                parts = Path(member.name).parts
                if not parts or parts[0] != "bundle":
                    raise ValueError(f"bundle archive member must be under bundle/: {member.name}")
                if member.issym() or member.islnk():
                    raise ValueError(f"bundle archive links are not allowed: {member.name}")
                if not (member.isdir() or member.isfile()):
                    raise ValueError(f"bundle archive member type is not allowed: {member.name}")
            for member in members:
                target = (extract_root / member.name).resolve()
                try:
                    target.relative_to(extract_root.resolve())
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
        extracted_bundle = extract_root / "bundle"
        if not (extracted_bundle / "public_testnet_manifest.json").is_file():
            raise ValueError("bundle archive did not contain public_testnet_manifest.json")
        if out_dir.exists():
            shutil.rmtree(out_dir)
        out_dir.parent.mkdir(parents=True, exist_ok=True)
        shutil.copytree(extracted_bundle, out_dir)


def _verify_synced_public_bundle_v0(bundle_root: Path) -> dict[str, Any]:
    public_manifest = _read_public_manifest(bundle_root)
    bootstrap_manifest_path = str(public_manifest.get("bootstrap_manifest_path", "bootstrap/manifest.json"))
    if not _is_safe_relative(bootstrap_manifest_path):
        raise ValueError("bootstrap_manifest_path must be relative and safe")
    bootstrap_root = Path(bootstrap_manifest_path).parent.as_posix()
    bootstrap_index = dict(_load_json_object(bundle_root / bootstrap_root / "mirror_index.json"))
    validate_mirror_index_v0(index=bootstrap_index, mirror_root=bundle_root / bootstrap_root)

    core_suite_path = str(public_manifest.get("core_suite_path", "core_features/feature_suite.json"))
    if not _is_safe_relative(core_suite_path):
        raise ValueError("core_suite_path must be relative and safe")
    feature_suite = _read_feature_suite(bundle_root, public_manifest)
    features = feature_suite.get("features")
    if not isinstance(features, list):
        raise ValueError("feature_suite.features must be a list")

    feature_indexes: list[dict[str, Any]] = []
    suite_root = Path(core_suite_path).parent
    for raw_feature in features:
        if not isinstance(raw_feature, Mapping):
            raise ValueError("feature entry must be an object")
        manifest_path = raw_feature.get("manifest_path")
        if not isinstance(manifest_path, str) or not _is_safe_relative(manifest_path):
            raise ValueError("feature manifest_path must be relative and safe")
        feature_root = (suite_root / Path(manifest_path).parent).as_posix()
        mirror_index_rel = str(raw_feature.get("mirror_index_path", "mirror_index.json"))
        if not _is_safe_relative(mirror_index_rel):
            raise ValueError("feature mirror_index_path must be relative and safe")
        index = dict(_load_json_object(bundle_root / feature_root / mirror_index_rel))
        validate_mirror_index_v0(index=index, mirror_root=bundle_root / feature_root)
        feature_indexes.append(index)

    return {
        "public_manifest": public_manifest,
        "feature_suite": feature_suite,
        "bootstrap_index": bootstrap_index,
        "feature_indexes": feature_indexes,
    }


def _safe_bundle_path(raw: object, *, bundle_root: Path, fallback: Path) -> Path:
    if isinstance(raw, str) and raw:
        path = Path(raw)
        if path.is_absolute() and path.exists():
            return path
        if not path.is_absolute() and ".." not in path.parts:
            candidate = bundle_root / path
            if candidate.exists():
                return candidate
    if fallback.exists():
        return fallback
    raise ValueError(f"missing bundle path: {fallback}")


def _header_heights(headers_dir: Path) -> list[int]:
    if not headers_dir.is_dir():
        return []
    heights: list[int] = []
    for path in headers_dir.glob("*.json"):
        try:
            heights.append(int(path.stem))
        except ValueError:
            continue
    return sorted(heights)


def _as_path(value: object, *, name: str) -> Path:
    if not isinstance(value, str) or value == "":
        raise ValueError(f"{name} must be a non-empty string path")
    return Path(value)


def _as_string_list(value: object, *, name: str) -> list[str]:
    if value is None:
        return []
    if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
        raise ValueError(f"{name} must be a list of strings")
    return list(value)


def _as_path_list(value: object, *, name: str) -> list[Path]:
    return [Path(item) for item in _as_string_list(value, name=name)]


def _is_http_url(value: str) -> bool:
    parsed = urlparse(value)
    return parsed.scheme in {"http", "https"} and bool(parsed.netloc) and not parsed.username and not parsed.password


def _tcp_port_available(host: str, port: int) -> bool:
    probe_host = "127.0.0.1" if host in {"", "0.0.0.0", "::"} else host
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
        sock.settimeout(0.2)
        try:
            return sock.connect_ex((probe_host, port)) != 0
        except OSError:
            return True


def _unique_strings(items: list[str]) -> list[str]:
    seen: set[str] = set()
    out: list[str] = []
    for item in items:
        if item not in seen:
            seen.add(item)
            out.append(item)
    return out


def _read_public_manifest(bundle_root: Path) -> dict[str, Any]:
    manifest_path = bundle_root / "public_testnet_manifest.json"
    obj = dict(_load_json_object(manifest_path))
    if obj.get("schema") != "zenodex.zeno_ledger.public_testnet_bundle.v0":
        raise ValueError("public testnet manifest schema mismatch")
    return obj


def _read_feature_suite(bundle_root: Path, public_manifest: Mapping[str, Any]) -> dict[str, Any]:
    suite_path = _safe_bundle_path(
        public_manifest.get("core_suite_path"),
        bundle_root=bundle_root,
        fallback=bundle_root / "core_features" / "feature_suite.json",
    )
    return dict(_load_json_object(suite_path))


def _extend_public_mirror_artifact_paths_v0(
    public_paths: list[str],
    *,
    mirror_root_rel: str,
    mirror_index: Mapping[str, Any],
) -> None:
    artifacts = mirror_index.get("artifacts")
    if not isinstance(artifacts, list):
        raise ValueError("mirror artifacts must be a list")
    for raw_entry in artifacts:
        if not isinstance(raw_entry, Mapping):
            raise ValueError("mirror artifact entry must be an object")
        rel = raw_entry.get("relative_path")
        if not isinstance(rel, str) or not _is_safe_relative(rel):
            raise ValueError("mirror artifact relative_path is unsafe")
        artifact_rel = str(Path(mirror_root_rel) / rel)
        if not _is_safe_relative(artifact_rel):
            raise ValueError("mirror artifact path is unsafe")
        public_paths.append(artifact_rel)


def _public_bundle_artifact_rel_paths_v0(bundle_root: Path) -> tuple[str, ...]:
    """Return bundle-relative artifact paths that are safe for public HTTP serving."""

    public_manifest = _read_public_manifest(bundle_root)
    public_paths: list[str] = ["public_testnet_manifest.json"]

    bootstrap_manifest_path = str(public_manifest.get("bootstrap_manifest_path", "bootstrap/manifest.json"))
    if not _is_safe_relative(bootstrap_manifest_path):
        raise ValueError("bootstrap_manifest_path must be relative and safe")
    public_paths.append(bootstrap_manifest_path)
    bootstrap_root = Path(bootstrap_manifest_path).parent.as_posix()
    bootstrap_index_rel = str(Path(bootstrap_root) / "mirror_index.json")
    public_paths.append(bootstrap_index_rel)
    bootstrap_index = dict(_load_json_object(bundle_root / bootstrap_index_rel))
    _extend_public_mirror_artifact_paths_v0(public_paths, mirror_root_rel=bootstrap_root, mirror_index=bootstrap_index)

    core_suite_path = str(public_manifest.get("core_suite_path", "core_features/feature_suite.json"))
    if not _is_safe_relative(core_suite_path):
        raise ValueError("core_suite_path must be relative and safe")
    public_paths.append(core_suite_path)
    feature_suite = dict(_load_json_object(bundle_root / core_suite_path))
    features = feature_suite.get("features")
    if not isinstance(features, list):
        raise ValueError("feature_suite.features must be a list")
    suite_root = Path(core_suite_path).parent
    for raw_feature in features:
        if not isinstance(raw_feature, Mapping):
            raise ValueError("feature entry must be an object")
        manifest_path = raw_feature.get("manifest_path")
        if not isinstance(manifest_path, str) or not _is_safe_relative(manifest_path):
            raise ValueError("feature manifest_path must be relative and safe")
        feature_root = (suite_root / Path(manifest_path).parent).as_posix()
        feature_manifest_rel = str(Path(feature_root) / Path(manifest_path).name)
        public_paths.append(feature_manifest_rel)
        mirror_index_rel = str(raw_feature.get("mirror_index_path", "mirror_index.json"))
        if not _is_safe_relative(mirror_index_rel):
            raise ValueError("feature mirror_index_path must be relative and safe")
        feature_index_rel = str(Path(feature_root) / mirror_index_rel)
        public_paths.append(feature_index_rel)
        feature_index = dict(_load_json_object(bundle_root / feature_index_rel))
        _extend_public_mirror_artifact_paths_v0(public_paths, mirror_root_rel=feature_root, mirror_index=feature_index)
    return tuple(_unique_strings(public_paths))


def _public_bundle_artifact_rel_for_request_v0(bundle_root: Path, request_rel: str) -> str | None:
    """Select a public bundle artifact by exact relative-path match."""

    if request_rel == PUBLIC_BUNDLE_ARCHIVE_NAME:
        return PUBLIC_BUNDLE_ARCHIVE_NAME
    for allowed_rel in _public_bundle_artifact_rel_paths_v0(bundle_root):
        if request_rel == allowed_rel:
            return allowed_rel
    return None


def _download_mirror_artifacts(
    *,
    base_url: str,
    out_root: Path,
    mirror_root_rel: str,
    mirror_index_rel: str,
) -> dict[str, Any]:
    """Download one mirror index and all artifacts it binds."""

    if not _is_safe_relative(mirror_root_rel):
        raise ValueError(f"unsafe mirror root: {mirror_root_rel}")
    if not _is_safe_relative(mirror_index_rel):
        raise ValueError(f"unsafe mirror index path: {mirror_index_rel}")
    index_path_rel = str(Path(mirror_root_rel) / mirror_index_rel)
    index = _download_json(base_url=base_url, rel_path=index_path_rel, out_root=out_root)
    artifacts = index.get("artifacts")
    if not isinstance(artifacts, list):
        raise ValueError(f"{index_path_rel} artifacts must be a list")
    for raw_entry in artifacts:
        if not isinstance(raw_entry, Mapping):
            raise ValueError(f"{index_path_rel} artifact entry must be an object")
        rel = raw_entry.get("relative_path")
        expected_sha = raw_entry.get("sha256")
        if not isinstance(rel, str) or not _is_safe_relative(rel):
            raise ValueError(f"{index_path_rel} artifact relative_path is unsafe")
        if not isinstance(expected_sha, str) or not expected_sha.startswith("0x"):
            raise ValueError(f"{index_path_rel} artifact sha256 is invalid")
        artifact_rel = str(Path(mirror_root_rel) / rel)
        data = _write_remote_file(base_url=base_url, rel_path=artifact_rel, out_root=out_root)
        if _sha256_bytes(data) != expected_sha:
            raise ValueError(f"artifact hash mismatch: {artifact_rel}")
    validate_mirror_index_v0(index=index, mirror_root=out_root / mirror_root_rel)
    return index


def sync_public_bundle_from_url_v0(
    *,
    base_url: str,
    out_dir: Path,
    bundle_archive_url: str | None = None,
    bundle_archive_sha256: str | None = None,
) -> dict[str, Any]:
    """Download and verify a public ZenoLedger bundle from an HTTP directory."""

    out_dir.mkdir(parents=True, exist_ok=True)
    used_bundle_archive = False
    if bundle_archive_url is not None or bundle_archive_sha256 is not None:
        if not isinstance(bundle_archive_url, str) or not _is_http_url(bundle_archive_url):
            raise ValueError("bundle_archive_url must be an http(s) URL without embedded credentials")
        if (
            not isinstance(bundle_archive_sha256, str)
            or not bundle_archive_sha256.startswith("0x")
            or len(bundle_archive_sha256) != 66
        ):
            raise ValueError("bundle_archive_sha256 must be a 0x-prefixed sha256 digest")
        archive_bytes = _fetch_remote_bytes(bundle_archive_url, max_bytes=MAX_REMOTE_BUNDLE_ARCHIVE_BYTES)
        if _sha256_bytes(archive_bytes) != bundle_archive_sha256:
            raise ValueError("bundle archive hash mismatch")
        _extract_public_bundle_archive_v0(archive_bytes=archive_bytes, out_dir=out_dir)
        used_bundle_archive = True
    else:
        public_manifest = _download_json(
            base_url=base_url,
            rel_path="public_testnet_manifest.json",
            out_root=out_dir,
        )
        if public_manifest.get("schema") != "zenodex.zeno_ledger.public_testnet_bundle.v0":
            raise ValueError("public testnet manifest schema mismatch")

        bootstrap_manifest_path = str(public_manifest.get("bootstrap_manifest_path", "bootstrap/manifest.json"))
        if not _is_safe_relative(bootstrap_manifest_path):
            raise ValueError("bootstrap_manifest_path must be relative and safe")
        bootstrap_root = Path(bootstrap_manifest_path).parent.as_posix()
        _download_mirror_artifacts(
            base_url=base_url,
            out_root=out_dir,
            mirror_root_rel=bootstrap_root,
            mirror_index_rel="mirror_index.json",
        )

        core_suite_path = str(public_manifest.get("core_suite_path", "core_features/feature_suite.json"))
        if not _is_safe_relative(core_suite_path):
            raise ValueError("core_suite_path must be relative and safe")
        feature_suite = _download_json(base_url=base_url, rel_path=core_suite_path, out_root=out_dir)
        features = feature_suite.get("features")
        if not isinstance(features, list):
            raise ValueError("feature_suite.features must be a list")

        suite_root = Path(core_suite_path).parent
        for raw_feature in features:
            if not isinstance(raw_feature, Mapping):
                raise ValueError("feature entry must be an object")
            manifest_path = raw_feature.get("manifest_path")
            if not isinstance(manifest_path, str) or not _is_safe_relative(manifest_path):
                raise ValueError("feature manifest_path must be relative and safe")
            feature_root = (suite_root / Path(manifest_path).parent).as_posix()
            mirror_index_rel = str(raw_feature.get("mirror_index_path", "mirror_index.json"))
            if not _is_safe_relative(mirror_index_rel):
                raise ValueError("feature mirror_index_path must be relative and safe")
            _download_mirror_artifacts(
                base_url=base_url,
                out_root=out_dir,
                mirror_root_rel=feature_root,
                mirror_index_rel=mirror_index_rel,
            )

    verified = _verify_synced_public_bundle_v0(out_dir)
    local_public_manifest = verified["public_manifest"]
    local_feature_suite = verified["feature_suite"]
    bootstrap_index = verified["bootstrap_index"]
    feature_indexes = verified["feature_indexes"]
    return {
        "schema": NODE_SYNC_REPORT_SCHEMA,
        "ok": True,
        "status": "accepted",
        "base_url": base_url,
        "bundle_root": str(out_dir),
        "used_bundle_archive": used_bundle_archive,
        "bundle_archive_url": bundle_archive_url if used_bundle_archive else None,
        "bundle_archive_sha256": bundle_archive_sha256 if used_bundle_archive else None,
        "network_id": local_public_manifest["network_id"],
        "chain_id": local_public_manifest["chain_id"],
        "bootstrap_mirror_index_hash": bootstrap_index["mirror_index_hash"],
        "feature_suite_hash": local_feature_suite["feature_suite_hash"],
        "feature_count": local_feature_suite["feature_count"],
        "feature_mirror_count": len(feature_indexes),
        "downloaded_mirror_count": 1 + len(feature_indexes),
        "downloaded_artifact_count": int(bootstrap_index["artifact_count"])
        + sum(int(index["artifact_count"]) for index in feature_indexes),
    }


def _node_status_hash(status: Mapping[str, Any]) -> str:
    body = {key: value for key, value in status.items() if key != "node_status_hash"}
    return hash_v0("node_status_v0", body)


def _public_network_config_hash_v0(config: Mapping[str, Any]) -> str:
    appended_fields = {
        "network_config_hash",
        "config_signer_registry",
        "config_signature_envelopes",
        "network_config_quorum_admission",
        "production_key_admission_receipt",
        "production_key_packet",
        "production_key_descriptors",
        "production_key_signature_envelopes",
    }
    body = {key: value for key, value in config.items() if key not in appended_fields}
    return hash_v0("public_network_config_v0", body)


def build_node_status_v0(
    *,
    bundle_root: Path,
    node_id: str,
    data_dir: Path,
    operator_report: Mapping[str, Any],
) -> dict[str, Any]:
    """Build a compact status object for a verified follower/watcher node."""

    public_manifest = _read_public_manifest(bundle_root)
    feature_suite = _read_feature_suite(bundle_root, public_manifest)
    bootstrap_manifest_path = _safe_bundle_path(
        public_manifest.get("bootstrap_manifest_path"),
        bundle_root=bundle_root,
        fallback=bundle_root / "bootstrap" / "manifest.json",
    )
    bootstrap_root = bootstrap_manifest_path.parent
    heights = _header_heights(bootstrap_root / "ledger" / "headers")
    latest_height = heights[-1] if heights else 0
    covered_features = list(operator_report.get("covered_features", []))
    body = {
        "schema": NODE_STATUS_SCHEMA,
        "ok": operator_report.get("ok") is True,
        "status": "accepted" if operator_report.get("ok") is True else "rejected",
        "node_id": node_id,
        "node_role": "follower_watcher",
        "network_id": public_manifest["network_id"],
        "chain_id": public_manifest["chain_id"],
        "bundle_root": str(bundle_root),
        "data_dir": str(data_dir),
        "latest_height": latest_height,
        "last_header_hash": operator_report.get("last_header_hash"),
        "last_app_hash": operator_report.get("last_app_hash"),
        "operator_attestation_path": operator_report.get("operator_attestation_path"),
        "operator_attestation_hash": operator_report.get("operator_attestation_hash"),
        "combined_testnet_status_path": operator_report.get("combined_testnet_status_path"),
        "combined_testnet_status_hash": operator_report.get("combined_testnet_status_hash"),
        "combined_watcher_count": operator_report.get("combined_watcher_count"),
        "mirror_index_hash": operator_report.get("mirror_index_hash"),
        "feature_suite_hash": operator_report.get("feature_suite_hash"),
        "covered_feature_count": len(covered_features),
        "covered_features": covered_features,
        "required_features": list(feature_suite.get("required_features", [])),
        "token_symbol": public_manifest.get("token_symbol"),
        "token_distribution": dict(public_manifest.get("token_distribution", {})),
        "token_distribution_hash": public_manifest.get("token_distribution_hash"),
        "tokenomics_posture": dict(public_manifest.get("tokenomics_posture", {})),
        "token_posture": dict(public_manifest.get("token_posture", {})),
        "test_token_catalog": list(public_manifest.get("test_token_catalog", [])),
        "testnet_faucet_posture": dict(public_manifest.get("testnet_faucet_posture", {})),
        "testnet_token_support": {
            "native_test_symbol": public_manifest.get("token_symbol"),
            "fixture_tokens": "core feature suites use deterministic test assets",
            "faucet_scope": "testnet-only feature lanes",
            "release_scope": str(dict(public_manifest.get("token_posture", {})).get("release_scope", "")),
        },
    }
    return {**body, "node_status_hash": hash_v0("node_status_v0", body)}


def run_node_once_v0(
    *,
    bundle_root: Path,
    node_id: str,
    data_dir: Path,
    observed_time_ms: int | None = None,
    peer_watcher_attestation_paths: list[Path] | None = None,
) -> dict[str, Any]:
    """Replay a bundle as a node and write node status artifacts."""

    peers = list(peer_watcher_attestation_paths or [])
    data_dir.mkdir(parents=True, exist_ok=True)
    operator_report = run_operator_rehearsal_v0(
        bundle_root=bundle_root,
        operator_id=node_id,
        out_dir=data_dir,
        observed_time_ms=observed_time_ms,
        peer_watcher_attestation_paths=peers,
    )
    operator_report_path = data_dir / "operator_rehearsal_report.json"
    _write_json(operator_report_path, operator_report)
    status = build_node_status_v0(
        bundle_root=bundle_root.resolve(),
        node_id=node_id,
        data_dir=data_dir.resolve(),
        operator_report=operator_report,
    )
    status_path = data_dir / "node_status.json"
    _write_json(status_path, status)
    return {
        "schema": NODE_REPORT_SCHEMA,
        "ok": operator_report.get("ok") is True and status.get("ok") is True,
        "status": "accepted" if operator_report.get("ok") is True and status.get("ok") is True else "rejected",
        "node_id": node_id,
        "node_status_path": str(status_path),
        "node_status_hash": status["node_status_hash"],
        "operator_rehearsal_report_path": str(operator_report_path),
        "operator_attestation_path": operator_report.get("operator_attestation_path"),
        "combined_testnet_status_path": operator_report.get("combined_testnet_status_path"),
        "combined_testnet_status_hash": operator_report.get("combined_testnet_status_hash"),
        "combined_watcher_count": operator_report.get("combined_watcher_count"),
        "latest_height": status["latest_height"],
        "covered_feature_count": status["covered_feature_count"],
        "covered_features": status["covered_features"],
    }


def _empty_evidence_v0() -> dict[str, list[object]]:
    return {
        "upba_certificates": [],
        "price_grid_tables": [],
        "uniform_batch_hypergraph_roots": [],
        "oracle_packets": [],
        "proof_receipts": [],
        "rejection_receipts": [],
    }


def _ingress_receipt_v0(
    *,
    chain_id: str,
    tx_hash: str,
    height: int,
    time_ms: int,
    sequencer_id: str,
) -> dict[str, Any]:
    body = {
        "schema": INGRESS_RECEIPT_SCHEMA_V0,
        "chain_id": chain_id,
        "tx_hash": tx_hash,
        "received_time_ms": time_ms,
        "received_sequence": height * 1_000,
        "sequencer_id": sequencer_id,
        "status": "included",
        "height": height,
        "index": 0,
        "reject_code": None,
    }
    return {**body, "receipt_hash": hash_v0("node_ingress_receipt_v0", body)}


def _body_for_tx_v0(
    *,
    chain_id: str,
    height: int,
    time_ms: int,
    sequencer_id: str,
    tx: Mapping[str, Any],
) -> dict[str, Any]:
    tx_obj = dict(tx)
    tx_hash = tx_hash_v0(tx_obj)
    body = {
        "schema": BODY_SCHEMA_V0,
        "chain_id": chain_id,
        "height": height,
        "ingress": {
            "batch_cutoff": {
                "schema": BATCH_CUTOFF_SCHEMA_V0,
                "chain_id": chain_id,
                "height": height,
                "cutoff_time_ms": time_ms,
                "cutoff_sequence": height * 1_000,
                "sequencer_id": sequencer_id,
                "policy_id": "zeno_ledger_node_live_append_v0",
                "policy_digest": hash_v0(
                    "node_live_append_policy_v0",
                    {"chain_id": chain_id, "policy_id": "zeno_ledger_node_live_append_v0"},
                ),
            },
            "ingress_receipts": [
                _ingress_receipt_v0(
                    chain_id=chain_id,
                    tx_hash=tx_hash,
                    height=height,
                    time_ms=time_ms,
                    sequencer_id=sequencer_id,
                )
            ],
            "forced_inclusion_requests": [],
            "forced_inclusion_decisions": [],
        },
        "transactions": [tx_obj],
        "settlement_envelopes": [],
        "evidence": _empty_evidence_v0(),
    }
    validate_body_v0(body)
    return body


def _read_http_json_body(handler: BaseHTTPRequestHandler) -> dict[str, Any]:
    raw_length = handler.headers.get("Content-Length")
    if raw_length is None:
        _raise_http_rejection(
            status=HTTPStatus.BAD_REQUEST,
            code=BAD_JSON,
            detail="Content-Length is required",
        )
    try:
        length = int(raw_length)
    except ValueError as exc:
        raise _HttpRejectedError(
            status=HTTPStatus.BAD_REQUEST,
            report=build_rejection_report_v0(
                BAD_JSON,
                "Content-Length must be an integer",
                error="Content-Length must be an integer",
            ),
        ) from exc
    if length < 0 or length > MAX_HTTP_POST_BYTES:
        _raise_http_rejection(
            status=HTTPStatus.REQUEST_ENTITY_TOO_LARGE,
            code=HTTP_POST_TOO_LARGE,
            detail="request body too large",
            max_http_post_bytes=MAX_HTTP_POST_BYTES,
            content_length=length,
        )
    payload = handler.rfile.read(length)
    try:
        obj = json.loads(payload.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise _HttpRejectedError(
            status=HTTPStatus.BAD_REQUEST,
            report=build_rejection_report_v0(
                BAD_JSON,
                "request body must be valid JSON",
                error="request body must be valid JSON",
            ),
        ) from exc
    if not isinstance(obj, dict):
        _raise_http_rejection(
            status=HTTPStatus.BAD_REQUEST,
            code=BAD_JSON,
            detail="request body must be a JSON object",
        )
    return obj


def _require_pubkey_v0(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise ValueError(f"{name} must be a string")
    return canonical_hex_fixed_allow_0x(value, nbytes=48, name=name)


def _require_asset_v0(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise ValueError(f"{name} must be a string")
    return canonical_hex_fixed_allow_0x(value, nbytes=32, name=name)


def _require_positive_amount_v0(value: object, *, name: str, maximum: int) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value <= 0:
        raise ValueError(f"{name} must be a positive int")
    if value > maximum:
        raise ValueError(f"{name} exceeds maximum")
    return int(value)


def _ui_amount_int_v0(value: object, *, name: str, maximum: int, allow_zero: bool = False) -> int:
    if isinstance(value, bool):
        raise ValueError(f"{name} must be an int")
    if isinstance(value, int):
        amount = value
    elif isinstance(value, float) and value.is_integer():
        amount = int(value)
    elif isinstance(value, str):
        stripped = value.strip()
        if stripped == "":
            raise ValueError(f"{name} must be an int")
        amount = int(stripped, 10)
    else:
        raise ValueError(f"{name} must be an int")
    if allow_zero:
        if amount < 0:
            raise ValueError(f"{name} must be a nonnegative int")
    elif amount <= 0:
        raise ValueError(f"{name} must be a positive int")
    if amount > maximum:
        raise ValueError(f"{name} exceeds maximum")
    return amount


def _latest_snapshot_for_ui_v0(
    *,
    data_dir: Path,
    node_status: Mapping[str, Any],
    use_reader_lock: bool = True,
) -> tuple[int, Mapping[str, Any]]:
    def _load_latest() -> tuple[int, Mapping[str, Any]]:
        bundle_root = Path(str(node_status["bundle_root"]))
        base = _live_base_paths(bundle_root=bundle_root, data_dir=data_dir, node_status=node_status)
        snapshot_path = Path(str(base["pre_snapshot_path"]))
        return int(base["latest_height"]), _dex_snapshot_from_state_file_obj_v0(_load_json_object(snapshot_path))

    if not use_reader_lock:
        return _load_latest()
    with _data_dir_reader_lock_v0(data_dir):
        return _load_latest()


def _ui_token_catalog_v0(node_status: Mapping[str, Any]) -> tuple[dict[str, str], dict[str, dict[str, str]]]:
    by_asset: dict[str, str] = {}
    by_symbol: dict[str, dict[str, str]] = {}
    raw_catalog = node_status.get("test_token_catalog", [])
    if not isinstance(raw_catalog, list):
        return by_asset, by_symbol
    for row in raw_catalog:
        if not isinstance(row, Mapping):
            continue
        raw_symbol = row.get("symbol")
        raw_display_symbol = row.get("display_symbol")
        raw_asset = row.get("asset_id")
        if not isinstance(raw_symbol, str) or not raw_symbol.strip() or not isinstance(raw_asset, str):
            continue
        try:
            asset = canonical_hex_fixed_allow_0x(raw_asset, nbytes=32, name="test_token_catalog.asset_id")
        except Exception:
            continue
        catalog_symbol = raw_symbol.strip()
        display_symbol = raw_display_symbol.strip() if isinstance(raw_display_symbol, str) and raw_display_symbol.strip() else catalog_symbol
        purpose = row.get("purpose")
        by_asset[asset] = display_symbol
        token = {
            "symbol": display_symbol,
            "asset_id": asset,
            "purpose": purpose if isinstance(purpose, str) else "",
        }
        by_symbol[display_symbol.upper()] = token
        by_symbol[catalog_symbol.upper()] = token
    return by_asset, by_symbol


def _protocol_token_asset_id_from_status_v0(node_status: Mapping[str, Any]) -> str | None:
    distribution = node_status.get("token_distribution")
    if isinstance(distribution, Mapping) and isinstance(distribution.get("token_asset_id"), str):
        return canonical_hex_fixed_allow_0x(distribution["token_asset_id"], nbytes=32, name="token_distribution.token_asset_id")
    catalog = node_status.get("test_token_catalog")
    catalog_rows = catalog if isinstance(catalog, list) else []
    for row in catalog_rows:
        if not isinstance(row, Mapping):
            continue
        if row.get("faucet_mint_allowed") is False and isinstance(row.get("asset_id"), str):
            return canonical_hex_fixed_allow_0x(row["asset_id"], nbytes=32, name="test_token_catalog.asset_id")
    return None


def _token_balance_sum_from_snapshot_v0(snapshot: Mapping[str, Any], *, asset_id: str) -> tuple[int, dict[str, int]]:
    balances = snapshot.get("balances")
    if not isinstance(balances, list):
        raise ValueError("snapshot balances must be a list")
    by_pubkey: dict[str, int] = {}
    total = 0
    for row in balances:
        if not isinstance(row, Mapping):
            continue
        if row.get("asset") != asset_id:
            continue
        pubkey = str(row.get("pubkey", ""))
        amount = row.get("amount")
        if not isinstance(amount, int) or isinstance(amount, bool) or amount < 0:
            raise ValueError("snapshot token balance amount must be nonnegative int")
        by_pubkey[pubkey] = by_pubkey.get(pubkey, 0) + int(amount)
        total += int(amount)
    pools = snapshot.get("pools")
    if isinstance(pools, list):
        for row in pools:
            if not isinstance(row, Mapping):
                continue
            if row.get("asset0") == asset_id:
                reserve0 = row.get("reserve0")
                if not isinstance(reserve0, int) or isinstance(reserve0, bool) or reserve0 < 0:
                    raise ValueError("snapshot token reserve0 amount must be nonnegative int")
                total += int(reserve0)
            if row.get("asset1") == asset_id:
                reserve1 = row.get("reserve1")
                if not isinstance(reserve1, int) or isinstance(reserve1, bool) or reserve1 < 0:
                    raise ValueError("snapshot token reserve1 amount must be nonnegative int")
                total += int(reserve1)
    return total, by_pubkey


def _tokenomics_buyback_market_routes_from_snapshot_v0(
    snapshot: Mapping[str, Any],
    *,
    token_asset_id: str,
) -> list[dict[str, Any]]:
    token_asset = canonical_hex_fixed_allow_0x(token_asset_id, nbytes=32, name="token_asset_id")
    pools = snapshot.get("pools")
    if not isinstance(pools, list):
        raise ValueError("snapshot pools must be a list")
    routes: list[dict[str, Any]] = []
    for row in pools:
        if not isinstance(row, Mapping):
            continue
        asset0 = _require_asset_v0(row.get("asset0"), name="pool.asset0")
        asset1 = _require_asset_v0(row.get("asset1"), name="pool.asset1")
        if token_asset not in {asset0, asset1}:
            continue
        status = str(row.get("status", ""))
        if status and status.lower() != "active":
            continue
        pool_id = str(row.get("pool_id", ""))
        if not pool_id:
            pool_id = compute_pool_id(asset0, asset1, int(row.get("fee_bps", 0)))
        quote_asset = asset1 if asset0 == token_asset else asset0
        routes.append(
            {
                "pool_id": pool_id,
                "token_asset_id": token_asset,
                "quote_asset_id": quote_asset,
                "fee_bps": int(row.get("fee_bps", 0)),
            }
        )
    return routes


def _ui_tokenomics_response_v0(*, data_dir: Path, node_status: Mapping[str, Any]) -> dict[str, Any]:
    distribution = node_status.get("token_distribution")
    if not isinstance(distribution, Mapping) or not distribution:
        return {
            "ok": False,
            "error": "token_distribution_missing",
            "production_security_claim": False,
        }
    distribution_obj = dict(distribution)
    validate_protocol_token_distribution_v0(distribution_obj)
    distribution_hash = str(distribution_obj.get("distribution_hash", ""))
    computed_distribution_hash = protocol_token_distribution_hash_v0(distribution_obj)
    manifest_distribution_hash = node_status.get("token_distribution_hash")
    manifest_hash_text = str(manifest_distribution_hash) if isinstance(manifest_distribution_hash, str) else distribution_hash
    hash_self_consistent = bool(distribution_hash) and distribution_hash == computed_distribution_hash
    hash_manifest_anchored = bool(manifest_hash_text) and manifest_hash_text == distribution_hash
    immutability = distribution_obj.get("immutability")
    immutability_obj = dict(immutability) if isinstance(immutability, Mapping) else {}
    height, snapshot = _latest_snapshot_for_ui_v0(data_dir=data_dir, node_status=node_status)
    token_asset_id = str(distribution_obj["token_asset_id"])
    circulating_supply, balances_by_pubkey = _token_balance_sum_from_snapshot_v0(snapshot, asset_id=token_asset_id)
    spent_by_program, claimed_keys = _tokenomics_claim_index_from_live_bodies_v0(data_dir=data_dir, max_height=height)
    buyback_index = _tokenomics_buyback_index_from_live_bodies_v0(data_dir=data_dir, max_height=height)
    initial_supply = int(distribution_obj["initial_supply"])
    supply_floor = int(distribution_obj["supply_floor"])
    burned_total = initial_supply - circulating_supply
    allocation_rows: list[dict[str, Any]] = []
    for allocation in distribution_obj["allocations"]:
        recipient = str(allocation["recipient_pubkey"])
        current_balance = int(balances_by_pubkey.get(recipient, 0))
        initial_amount = int(allocation["amount"])
        allocation_rows.append(
            {
                "id": str(allocation["id"]),
                "category": str(allocation["category"]),
                "recipient_role": str(allocation["recipient_role"]),
                "recipient_pubkey": recipient,
                "initial_amount": initial_amount,
                "share_bps": int(allocation["share_bps"]),
                "current_balance": current_balance,
            }
        )
    active_program_rows: list[dict[str, Any]] = []
    for program in distribution_obj.get("active_participant_programs", []):
        if not isinstance(program, Mapping):
            continue
        claimed_amount = int(spent_by_program.get(str(program["id"]), 0))
        budget_amount = int(program["budget_amount"])
        active_program_rows.append(
            {
                "id": str(program["id"]),
                "category": str(program["category"]),
                "budget_amount": budget_amount,
                "claimed_amount": claimed_amount,
                "remaining_amount": max(0, budget_amount - claimed_amount),
                "share_bps_of_reward_pool": int(program["share_bps_of_reward_pool"]),
                "claim_amount": int(program["claim_amount"]),
                "reward_source_allocation_id": str(program["reward_source_allocation_id"]),
                "controller_role": str(program["controller_role"]),
                "controller_pubkey": str(program["controller_pubkey"]),
                "eligibility_receipts": list(program.get("eligibility_receipts", [])),
            }
        )
    supply_conserved_or_deflated = 0 <= burned_total <= initial_supply
    floor_preserved = circulating_supply >= supply_floor
    immutability_checks_pass = (
        immutability_obj.get("post_genesis_mutation_allowed") is False
        and immutability_obj.get("runtime_mutation_allowed") is False
        and immutability_obj.get("python_override_allowed_after_genesis") is False
    )
    policy_flags = dict(distribution_obj.get("tau_policy", {})).get("host_computed_flags", {})
    dex_config = _local_testnet_tokenomics_dex_config_v0(node_status)
    buyback_market_routes = _tokenomics_buyback_market_routes_from_snapshot_v0(
        snapshot,
        token_asset_id=token_asset_id,
    )
    buyback_market_purchase_available = bool(buyback_market_routes)
    buyback_market_purchase_runtime_enabled = buyback_market_purchase_available
    buyback_market_purchase_runtime_mode = (
        "market_purchase_then_burn"
        if buyback_market_purchase_runtime_enabled
        else "treasury_allocation_burn_only"
    )
    buyback_market_purchase_runtime_blocker = None if buyback_market_purchase_runtime_enabled else "token_buyback_route_unavailable"
    status = {
        "schema": "zenodex.zeno_ledger.tokenomics_status.v0",
        "ok": (
            supply_conserved_or_deflated
            and floor_preserved
            and hash_self_consistent
            and hash_manifest_anchored
            and immutability_checks_pass
        ),
        "height": int(height),
        "chain_id": str(node_status.get("chain_id", "")),
        "token_symbol": str(distribution_obj["token_symbol"]),
        "token_asset_id": token_asset_id,
        "initial_supply": initial_supply,
        "current_supply": circulating_supply,
        "circulating_supply": circulating_supply,
        "burned_total": burned_total,
        "buyback_burned_total": int(buyback_index["buyback_burned_total"]),
        "buyback_total_swap_fee": int(buyback_index["buyback_total_swap_fee"]),
        "buyback_carry_after": int(buyback_index["buyback_carry_after"]),
        "buyback_event_count": int(buyback_index["buyback_event_count"]),
        "buyback_share_bps": LOCAL_TESTNET_BUYBACK_SHARE_BPS,
        "buyback_source_allocation_id": LOCAL_TESTNET_BUYBACK_SOURCE_ALLOCATION_ID,
        "protocol_fee_capture": {
            "enabled": int(dex_config.protocol_fee_share_bps) > 0,
            "share_bps": int(dex_config.protocol_fee_share_bps),
            "recipient_pubkey": dex_config.protocol_fee_recipient_pubkey,
        },
        "buyback_market_purchase": {
            "available": buyback_market_purchase_available,
            "route_available": buyback_market_purchase_available,
            "route_count": len(buyback_market_routes),
            "routes": buyback_market_routes,
            "runtime_enabled": buyback_market_purchase_runtime_enabled,
            "runtime_mode": buyback_market_purchase_runtime_mode,
            "runtime_blocker": buyback_market_purchase_runtime_blocker,
            "production_ready": False,
        },
        "supply_floor": supply_floor,
        "allocation_total": int(distribution_obj["allocation_total"]),
        "allocation_rows": allocation_rows,
        "active_participant_reward_pool_id": str(distribution_obj["active_participant_reward_pool_id"]),
        "active_participant_programs": active_program_rows,
        "immutability": immutability_obj,
        "tau_policy": dict(distribution_obj.get("tau_policy", {})),
        "checks": {
            "distribution_manifest_present": True,
            "distribution_hash_self_consistent": hash_self_consistent,
            "distribution_hash_manifest_anchored": hash_manifest_anchored,
            "post_genesis_mutation_disabled": immutability_obj.get("post_genesis_mutation_allowed") is False,
            "runtime_mutation_disabled": immutability_obj.get("runtime_mutation_allowed") is False,
            "python_override_disabled_after_genesis": immutability_obj.get("python_override_allowed_after_genesis") is False,
            "immutability_checks_pass": immutability_checks_pass,
            "allocation_sum_matches_initial_supply": int(distribution_obj["allocation_total"]) == initial_supply,
            "active_participant_programs_sum_to_pool": (
                isinstance(policy_flags, Mapping) and policy_flags.get("active_programs_sum_to_pool") is True
            ),
            "tau_policy_flags_all_pass": bool(policy_flags) and all(policy_flags.values()) if isinstance(policy_flags, Mapping) else False,
            "protocol_token_faucet_mint_allowed": False,
            "external_minting_allowed": False,
            "supply_conserved_or_deflated": supply_conserved_or_deflated,
            "floor_preserved": floor_preserved,
            "active_participant_claims_indexed": len(claimed_keys),
            "buyback_burned_total_matches_supply_delta": int(buyback_index["buyback_burned_total"]) <= burned_total,
            "buyback_market_route_available": buyback_market_purchase_available,
            "buyback_market_purchase_runtime_enabled": buyback_market_purchase_runtime_enabled,
        },
        "tokenomics_posture": dict(node_status.get("tokenomics_posture", {})),
        "distribution_hash": distribution_hash,
        "computed_distribution_hash": computed_distribution_hash,
        "manifest_distribution_hash": manifest_hash_text,
        "production_security_claim": False,
    }
    return {"ok": bool(status["ok"]), "status": status}


def _is_tokenomics_reward_claim_body_v0(body: Mapping[str, Any]) -> bool:
    txs = body.get("transactions")
    if not isinstance(txs, list) or len(txs) != 1 or not isinstance(txs[0], Mapping):
        return False
    return txs[0].get("kind") == TOKENOMICS_REWARD_CLAIM_KIND


def _tokenomics_claim_index_from_live_bodies_v0(*, data_dir: Path, max_height: int) -> tuple[dict[str, int], set[str]]:
    spent_by_program: dict[str, int] = {}
    claimed_keys: set[str] = set()
    bodies_dir = data_dir / "live_ledger" / "bodies"
    if not bodies_dir.is_dir():
        return spent_by_program, claimed_keys
    for path in sorted(bodies_dir.glob("*.json"), key=lambda item: int(item.stem) if item.stem.isdigit() else -1):
        if not path.stem.isdigit():
            continue
        height = int(path.stem)
        if height <= 0 or height > max_height:
            continue
        body = _load_json_object(path)
        if not _is_tokenomics_reward_claim_body_v0(body):
            continue
        tx = body["transactions"][0]
        if not isinstance(tx, Mapping):
            raise ValueError(f"tokenomics claim body {height} transaction malformed")
        claim = tx.get("claim")
        if not isinstance(claim, Mapping):
            raise ValueError(f"tokenomics claim body {height} missing claim")
        program_id = str(claim.get("program_id", ""))
        amount = claim.get("amount")
        claim_key = claim.get("claim_key")
        if not program_id or not isinstance(amount, int) or isinstance(amount, bool) or amount <= 0:
            raise ValueError(f"tokenomics claim body {height} has invalid amount")
        if not isinstance(claim_key, str) or not claim_key:
            raise ValueError(f"tokenomics claim body {height} has invalid claim_key")
        spent_by_program[program_id] = spent_by_program.get(program_id, 0) + int(amount)
        claimed_keys.add(claim_key)
    return spent_by_program, claimed_keys


def _tokenomics_buyback_event_from_tx_v0(tx: Mapping[str, Any]) -> Mapping[str, Any] | None:
    operations = tx.get("operations")
    if not isinstance(operations, Mapping):
        return None
    raw_events = operations.get(TOKENOMICS_BUYBACK_BURN_OP_STREAM)
    if raw_events is None:
        return None
    if not isinstance(raw_events, list) or len(raw_events) != 1 or not isinstance(raw_events[0], Mapping):
        raise ValueError("tokenomics buyback burn operation malformed")
    operation = raw_events[0]
    if operation.get("kind") != TOKENOMICS_BUYBACK_BURN_OP_KIND:
        raise ValueError("tokenomics buyback burn operation kind mismatch")
    event = operation.get("event")
    if not isinstance(event, Mapping):
        raise ValueError("tokenomics buyback burn operation event missing")
    return event


def _tokenomics_buyback_index_from_live_bodies_v0(*, data_dir: Path, max_height: int) -> dict[str, int]:
    total_fee = 0
    burned_total = 0
    carry_after = 0
    event_count = 0
    bodies_dir = data_dir / "live_ledger" / "bodies"
    if not bodies_dir.is_dir():
        return {
            "buyback_total_swap_fee": 0,
            "buyback_burned_total": 0,
            "buyback_carry_after": 0,
            "buyback_event_count": 0,
        }
    for path in sorted(bodies_dir.glob("*.json"), key=lambda item: int(item.stem) if item.stem.isdigit() else -1):
        if not path.stem.isdigit():
            continue
        height = int(path.stem)
        if height <= 0 or height > max_height:
            continue
        body = _load_json_object(path)
        txs = body.get("transactions")
        if not isinstance(txs, list):
            continue
        for tx in txs:
            if not isinstance(tx, Mapping):
                continue
            event = _tokenomics_buyback_event_from_tx_v0(tx)
            if event is None:
                continue
            total_fee += int(event.get("total_swap_fee", 0))
            burned_total += int(event.get("burn_amount", 0))
            carry_after = int(event.get("carry_after", 0))
            event_count += 1
    return {
        "buyback_total_swap_fee": total_fee,
        "buyback_burned_total": burned_total,
        "buyback_carry_after": carry_after,
        "buyback_event_count": event_count,
    }


def _ui_pool_analytics_from_live_bodies_v0(
    *,
    data_dir: Path,
    max_height: int,
    window_seconds: int = 86_400,
    max_blocks: int = 10_000,
) -> dict[str, Any]:
    bodies_dir = data_dir / "live_ledger" / "bodies"
    receipts_dir = data_dir / "live_ledger" / "receipts"
    if max_height <= 0 or not bodies_dir.is_dir() or not receipts_dir.is_dir():
        return {"by_pool": {}, "window": None}

    paths = [
        path
        for path in bodies_dir.glob("*.json")
        if path.stem.isdigit() and 0 < int(path.stem) <= max_height
    ]
    paths = sorted(paths, key=lambda item: int(item.stem))[-max_blocks:]
    if not paths:
        return {"by_pool": {}, "window": None}

    loaded: list[tuple[int, Mapping[str, Any]]] = []
    max_seen_ts: int | None = None
    for path in paths:
        height = int(path.stem)
        body = _load_json_object(path)
        raw_ts = None
        txs = body.get("transactions")
        if isinstance(txs, list):
            for tx in txs:
                if isinstance(tx, Mapping) and isinstance(tx.get("block_timestamp"), int) and not isinstance(tx.get("block_timestamp"), bool):
                    raw_ts = int(tx["block_timestamp"])
                    break
        if raw_ts is None:
            cutoff = body.get("ingress", {}).get("batch_cutoff") if isinstance(body.get("ingress"), Mapping) else None
            if isinstance(cutoff, Mapping) and isinstance(cutoff.get("cutoff_time_ms"), int):
                raw_ts = int(cutoff["cutoff_time_ms"]) // 1000
        if raw_ts is not None:
            max_seen_ts = raw_ts if max_seen_ts is None else max(max_seen_ts, raw_ts)
        loaded.append((height, body))

    min_seen_ts = None if max_seen_ts is None else max_seen_ts - max(0, int(window_seconds))
    by_pool: dict[str, dict[str, int]] = {}

    for height, body in loaded:
        txs = body.get("transactions")
        if not isinstance(txs, list):
            continue
        tx_ts = None
        if txs and isinstance(txs[0], Mapping) and isinstance(txs[0].get("block_timestamp"), int):
            tx_ts = int(txs[0]["block_timestamp"])
        if min_seen_ts is not None and tx_ts is not None and tx_ts < min_seen_ts:
            continue
        receipts_path = receipts_dir / f"{height}.json"
        if not receipts_path.is_file():
            continue
        try:
            receipts = json.loads(receipts_path.read_text(encoding="utf-8"))
        except Exception:
            continue
        if not isinstance(receipts, list):
            continue
        for tx_index, tx in enumerate(txs):
            if not isinstance(tx, Mapping):
                continue
            receipt = receipts[tx_index] if tx_index < len(receipts) and isinstance(receipts[tx_index], Mapping) else None
            if receipt is None or receipt.get("accepted") is not True or receipt.get("state_changed") is not True:
                continue
            operations = tx.get("operations")
            if not isinstance(operations, Mapping):
                continue
            swap_ops = operations.get("5")
            if not isinstance(swap_ops, list):
                continue
            buyback_event = _tokenomics_buyback_event_from_tx_v0(tx)
            fee_units = None
            if buyback_event is not None and isinstance(buyback_event.get("total_swap_fee"), int):
                fee_units = max(0, int(buyback_event["total_swap_fee"]))
            for op in swap_ops:
                if not isinstance(op, Mapping) or op.get("kind") != "SWAP_EXACT_IN":
                    continue
                raw_pool_id = op.get("pool_id")
                raw_asset_in = op.get("asset_in")
                raw_amount_in = op.get("amount_in")
                if not isinstance(raw_pool_id, str) or not isinstance(raw_asset_in, str):
                    continue
                if not isinstance(raw_amount_in, int) or isinstance(raw_amount_in, bool) or raw_amount_in <= 0:
                    continue
                pool_row = by_pool.setdefault(
                    raw_pool_id,
                    {
                        "swap_count_24h": 0,
                        "input_volume0_24h": 0,
                        "input_volume1_24h": 0,
                        "fee0_24h": 0,
                        "fee1_24h": 0,
                        "input_volume_by_asset_24h": {},
                        "fee_by_asset_24h": {},
                    },
                )
                pool_row["swap_count_24h"] += 1
                volume_by_asset = pool_row["input_volume_by_asset_24h"]
                fee_by_asset = pool_row["fee_by_asset_24h"]
                if isinstance(volume_by_asset, dict):
                    volume_by_asset[raw_asset_in] = int(volume_by_asset.get(raw_asset_in, 0)) + int(raw_amount_in)
                volume_key = "input_volume0_24h" if raw_asset_in < str(op.get("asset_out", "")) else "input_volume1_24h"
                fee_key = "fee0_24h" if volume_key == "input_volume0_24h" else "fee1_24h"
                pool_row[volume_key] += int(raw_amount_in)
                if fee_units is not None and len(swap_ops) == 1:
                    pool_row[fee_key] += int(fee_units)
                    if isinstance(fee_by_asset, dict):
                        fee_by_asset[raw_asset_in] = int(fee_by_asset.get(raw_asset_in, 0)) + int(fee_units)

    return {
        "by_pool": by_pool,
        "window": {
            "kind": "ledger_timestamp_last_24h",
            "seconds": int(window_seconds),
            "from_block_timestamp": min_seen_ts,
            "to_block_timestamp": max_seen_ts,
            "max_blocks": int(max_blocks),
        },
    }


def _tokenomics_buyback_source_pubkey_v0(distribution: Mapping[str, Any]) -> str:
    for allocation in distribution.get("allocations", []):
        if isinstance(allocation, Mapping) and allocation.get("id") == LOCAL_TESTNET_BUYBACK_SOURCE_ALLOCATION_ID:
            return _require_pubkey_v0(allocation.get("recipient_pubkey"), name="buyback.source_pubkey")
    raise ValueError("buyback source allocation missing")


def _local_testnet_tokenomics_dex_config_v0(node_status: Mapping[str, Any]) -> DexConfig:
    distribution = node_status.get("token_distribution")
    if not isinstance(distribution, Mapping) or not distribution:
        return DexConfig()
    distribution_obj = dict(distribution)
    validate_protocol_token_distribution_v0(distribution_obj)
    source_pubkey = _tokenomics_buyback_source_pubkey_v0(distribution_obj)
    return DexConfig(
        protocol_fee_share_bps=LOCAL_TESTNET_BUYBACK_SHARE_BPS,
        protocol_fee_recipient_pubkey=source_pubkey,
    )


def _compute_dex_total_swap_fee_for_tx_v0(
    *,
    pre_snapshot: Mapping[str, Any],
    tx: Mapping[str, Any],
    chain_id: str,
    dex_config: DexConfig | None = None,
    min_lp_position_age_seconds: int,
    lp_duration_risk_policy: Any | None,
) -> int | None:
    operations = tx.get("operations")
    if not isinstance(operations, Mapping):
        return None
    result = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=True,
            require_intent_signatures=True,
            allow_unsigned_intents_if_tx_sender_matches=False,
            chain_id=chain_id,
            dex_config=dex_config or DexConfig(),
            min_lp_position_age_seconds=min_lp_position_age_seconds,
            lp_duration_risk_policy=lp_duration_risk_policy,
        ),
        state=state_from_snapshot(pre_snapshot),
        operations=dict(operations),
        block_timestamp=int(tx.get("block_timestamp", 0)),
        tx_sender_pubkey=tx.get("tx_sender_pubkey") if isinstance(tx.get("tx_sender_pubkey"), str) else None,
    )
    if not result.ok or result.settlement is None:
        return None
    return sum(int(fill.fee_paid or 0) for fill in result.settlement.fills)


def _compute_dex_result_for_tokenomics_tx_v0(
    *,
    pre_snapshot: Mapping[str, Any],
    tx: Mapping[str, Any],
    chain_id: str,
    dex_config: DexConfig,
    min_lp_position_age_seconds: int,
    lp_duration_risk_policy: Any | None,
) -> Any | None:
    operations = tx.get("operations")
    if not isinstance(operations, Mapping):
        return None
    normalized_operations = _normalize_dex_operations_for_apply_v0(dict(operations))
    result = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=True,
            require_intent_signatures=True,
            allow_unsigned_intents_if_tx_sender_matches=False,
            chain_id=chain_id,
            dex_config=dex_config,
            min_lp_position_age_seconds=min_lp_position_age_seconds,
            lp_duration_risk_policy=lp_duration_risk_policy,
        ),
        state=state_from_snapshot(pre_snapshot),
        operations=normalized_operations,
        block_timestamp=int(tx.get("block_timestamp", 0)),
        tx_sender_pubkey=tx.get("tx_sender_pubkey") if isinstance(tx.get("tx_sender_pubkey"), str) else None,
    )
    if not result.ok or result.settlement is None or result.state is None:
        return None
    return result


def _protocol_fee_by_asset_from_result_v0(result: Any, tx: Mapping[str, Any]) -> dict[str, int]:
    settlement = result.settlement
    if settlement is None:
        return {}
    operations = tx.get("operations")
    raw_intents = operations.get("5") if isinstance(operations, Mapping) else None
    intents_by_id: dict[str, Mapping[str, Any]] = {}
    if isinstance(raw_intents, list):
        for intent in raw_intents:
            if isinstance(intent, Mapping) and isinstance(intent.get("intent_id"), str):
                intents_by_id[str(intent["intent_id"])] = intent
    by_asset: dict[str, int] = {}
    for fill in settlement.fills:
        protocol_fee = int(fill.protocol_fee_paid or 0)
        if protocol_fee <= 0:
            continue
        intent = intents_by_id.get(str(fill.intent_id))
        asset_in = intent.get("asset_in") if isinstance(intent, Mapping) else None
        if isinstance(asset_in, str):
            by_asset[asset_in] = by_asset.get(asset_in, 0) + protocol_fee
    return by_asset


def _market_buyback_purchase_from_state_v0(
    *,
    state: Any,
    source_pubkey: str,
    token_asset_id: str,
    protocol_fee_by_asset: Mapping[str, int],
    current_supply_before: int,
    supply_floor: int,
) -> dict[str, Any] | None:
    routes: list[tuple[str, Any, str, int]] = []
    for pool_id, pool in state.pools.items():
        raw_status = getattr(pool, "status", "")
        status_text = str(getattr(raw_status, "value", raw_status)).lower()
        if status_text != "active":
            continue
        asset0 = str(pool.asset0)
        asset1 = str(pool.asset1)
        if token_asset_id not in {asset0, asset1}:
            continue
        quote_asset = asset1 if asset0 == token_asset_id else asset0
        amount_in = int(protocol_fee_by_asset.get(quote_asset, 0))
        if amount_in <= 0:
            continue
        if int(state.balances.get(source_pubkey, quote_asset)) < amount_in:
            continue
        routes.append((str(pool_id), pool, quote_asset, amount_in))
    for pool_id, pool, quote_asset, amount_in in sorted(routes, key=lambda item: (item[2], item[0])):
        if quote_asset == pool.asset0:
            reserve_in_before = int(pool.reserve0)
            reserve_out_before = int(pool.reserve1)
            quote_side = "asset0"
        else:
            reserve_in_before = int(pool.reserve1)
            reserve_out_before = int(pool.reserve0)
            quote_side = "asset1"
        try:
            amount_out, (reserve_in_after, reserve_out_after) = swap_exact_in_for_pool(
                pool,
                reserve_in=reserve_in_before,
                reserve_out=reserve_out_before,
                amount_in=amount_in,
            )
        except Exception:
            continue
        amount_out = int(amount_out)
        if amount_out <= 0:
            continue
        if current_supply_before - amount_out < supply_floor:
            continue
        if quote_side == "asset0":
            reserve0_after = int(reserve_in_after)
            reserve1_after = int(reserve_out_after)
        else:
            reserve0_after = int(reserve_out_after)
            reserve1_after = int(reserve_in_after)
        return {
            "pool_id": pool_id,
            "quote_asset_id": quote_asset,
            "token_asset_id": token_asset_id,
            "quote_amount_in": amount_in,
            "token_amount_out": amount_out,
            "pool_fee_bps": int(pool.fee_bps),
            "pool_curve_tag": str(pool.curve_tag),
            "pool_curve_params": str(pool.curve_params),
            "reserve0_before": int(pool.reserve0),
            "reserve1_before": int(pool.reserve1),
            "reserve0_after": reserve0_after,
            "reserve1_after": reserve1_after,
        }
    return None


def _attach_tokenomics_buyback_burn_event_v0(
    *,
    tx: Mapping[str, Any],
    pre_snapshot: Mapping[str, Any],
    node_status: Mapping[str, Any],
    chain_id: str,
    height: int,
    tx_index: int,
    data_dir: Path,
    min_lp_position_age_seconds: int,
    lp_duration_risk_policy: Any | None,
) -> dict[str, Any]:
    tx_obj = json.loads(json.dumps(tx))
    if _tokenomics_buyback_event_from_tx_v0(tx_obj) is not None:
        return tx_obj
    distribution = node_status.get("token_distribution")
    if not isinstance(distribution, Mapping) or not distribution:
        return tx_obj
    distribution_obj = dict(distribution)
    validate_protocol_token_distribution_v0(distribution_obj)
    dex_config = _local_testnet_tokenomics_dex_config_v0(node_status)
    result = _compute_dex_result_for_tokenomics_tx_v0(
        pre_snapshot=pre_snapshot,
        tx=tx_obj,
        chain_id=chain_id,
        dex_config=dex_config,
        min_lp_position_age_seconds=min_lp_position_age_seconds,
        lp_duration_risk_policy=lp_duration_risk_policy,
    )
    if result is None or result.settlement is None or result.state is None:
        return tx_obj
    total_fee = sum(int(fill.fee_paid or 0) for fill in result.settlement.fills)
    if total_fee <= 0:
        return tx_obj
    token_asset_id = str(distribution_obj["token_asset_id"])
    result_snapshot = snapshot_from_state(result.state).data
    current_supply, balances_by_pubkey = _token_balance_sum_from_snapshot_v0(result_snapshot, asset_id=token_asset_id)
    buyback_index = _tokenomics_buyback_index_from_live_bodies_v0(data_dir=data_dir, max_height=height - 1)
    source_pubkey = _tokenomics_buyback_source_pubkey_v0(distribution_obj)
    market_purchase = _market_buyback_purchase_from_state_v0(
        state=result.state,
        source_pubkey=source_pubkey,
        token_asset_id=token_asset_id,
        protocol_fee_by_asset=_protocol_fee_by_asset_from_result_v0(result, tx_obj),
        current_supply_before=current_supply,
        supply_floor=int(distribution_obj["supply_floor"]),
    )
    execution_mode = "market_purchase_then_burn" if market_purchase is not None else "treasury_allocation_burn_only"
    event = build_tokenomics_buyback_burn_event_v0(
        distribution=distribution_obj,
        chain_id=chain_id,
        height=height,
        tx_index=tx_index,
        tx_hash=tx_hash_v0(tx_obj),
        total_swap_fee=total_fee,
        carry_before=int(buyback_index["buyback_carry_after"]),
        source_balance_before=int(balances_by_pubkey.get(source_pubkey, 0)),
        current_supply_before=current_supply,
        buyback_share_bps=LOCAL_TESTNET_BUYBACK_SHARE_BPS,
        source_allocation_id=LOCAL_TESTNET_BUYBACK_SOURCE_ALLOCATION_ID,
        execution_mode=execution_mode,
        market_purchase=market_purchase,
        production_security_claim=False,
    )
    operations = tx_obj.setdefault("operations", {})
    if not isinstance(operations, dict):
        raise ValueError("transactions.operations must be an object")
    operations[TOKENOMICS_BUYBACK_BURN_OP_STREAM] = [
        {
            "module": "ZenoTokenomics",
            "kind": TOKENOMICS_BUYBACK_BURN_OP_KIND,
            "event": event,
        }
    ]
    return tx_obj


def _ledger_body_and_receipts_paths_v0(*, data_dir: Path, height: int) -> tuple[Path, Path]:
    live_body = data_dir / "live_ledger" / "bodies" / f"{height}.json"
    live_receipts = data_dir / "live_ledger" / "receipts" / f"{height}.json"
    # Height is parsed as a bounded integer and data_dir is the local node data root.
    if _artifact_is_file_v0(live_body) and _artifact_is_file_v0(live_receipts):
        return live_body, live_receipts
    node_status = load_node_status_v0(data_dir)
    bundle_root = Path(str(node_status["bundle_root"]))
    bootstrap_body = bundle_root / "bootstrap" / "ledger" / "bodies" / f"{height}.json"
    bootstrap_receipts = bundle_root / "bootstrap" / "ledger" / "receipts" / f"{height}.json"
    return bootstrap_body, bootstrap_receipts


def _strip_node_dex_sidecars_v0(tx: Mapping[str, Any]) -> dict[str, Any]:
    tx_obj = json.loads(json.dumps(tx))
    operations = tx_obj.get("operations")
    if isinstance(operations, dict):
        operations.pop(TOKENOMICS_BUYBACK_BURN_OP_STREAM, None)
    return tx_obj


def _default_ui_intent_tx_id_v0(*, prefix: str, sender: str, nonce: int, intent_payload: Mapping[str, Any]) -> str:
    """Stable implicit tx id for UI actions when the client omits one."""
    digest = hash_v0(
        "zeno_ledger_ui_default_tx_id_v0",
        {
            "prefix": prefix,
            "sender_pubkey": sender,
            "nonce": nonce,
            "intent_payload": intent_payload,
        },
    )
    sender_tag = sender.lower().removeprefix("0x")[:12]
    return f"{prefix}-{nonce}-{sender_tag}-{digest.removeprefix('0x')[:24]}"


def _existing_append_report_for_tx_id_v0(
    *,
    data_dir: Path,
    tx_id: str,
    tx: Mapping[str, Any],
    max_height: int,
) -> dict[str, Any] | None:
    normalized_tx_id = tx_id.strip()
    if not normalized_tx_id:
        return None
    incoming_core = _strip_node_dex_sidecars_v0(tx)
    bodies_dir = data_dir / "live_ledger" / "bodies"
    if not bodies_dir.is_dir():
        return None
    for path in sorted(bodies_dir.glob("*.json"), key=lambda item: int(item.stem) if item.stem.isdigit() else -1):
        if not path.stem.isdigit():
            continue
        height = int(path.stem)
        if height <= 0 or height > max_height:
            continue
        body = _load_json_object(path)
        txs = body.get("transactions")
        if not isinstance(txs, list):
            continue
        for existing_tx_raw in txs:
            if not isinstance(existing_tx_raw, Mapping):
                continue
            if str(existing_tx_raw.get("tx_id", "")).strip() != normalized_tx_id:
                continue
            existing_core = _strip_node_dex_sidecars_v0(existing_tx_raw)
            if existing_core != incoming_core:
                raise ValueError("duplicate_tx_id_payload_mismatch")
            append_report_path = data_dir / "append_reports" / f"{height}.json"
            if append_report_path.is_file():
                report_obj = dict(_load_json_object(append_report_path))
            else:
                _body_path, receipts_path = _ledger_body_and_receipts_paths_v0(data_dir=data_dir, height=height)
                receipts = json.loads(receipts_path.read_text(encoding="utf-8"))
                report_obj = {
                    "schema": NODE_APPEND_REPORT_SCHEMA,
                    "ok": True,
                    "status": "accepted",
                    "height": height,
                    "tx_hash": tx_hash_v0(dict(existing_tx_raw)),
                    "body_path": str(path),
                    "receipts_path": str(receipts_path),
                    "receipt": receipts[0] if isinstance(receipts, list) and receipts else None,
                }
            report_obj["idempotent_replay"] = True
            return report_obj
    return None


def _existing_tx_and_append_report_for_tx_id_v0(
    *,
    data_dir: Path,
    tx_id: str,
    max_height: int,
) -> tuple[dict[str, Any], dict[str, Any]] | None:
    normalized_tx_id = tx_id.strip()
    if not normalized_tx_id:
        return None
    bodies_dir = data_dir / "live_ledger" / "bodies"
    if not bodies_dir.is_dir():
        return None
    for path in sorted(bodies_dir.glob("*.json"), key=lambda item: int(item.stem) if item.stem.isdigit() else -1):
        if not path.stem.isdigit():
            continue
        height = int(path.stem)
        if height <= 0 or height > max_height:
            continue
        body = _load_json_object(path)
        txs = body.get("transactions")
        if not isinstance(txs, list):
            continue
        for existing_tx_raw in txs:
            if not isinstance(existing_tx_raw, Mapping):
                continue
            if str(existing_tx_raw.get("tx_id", "")).strip() != normalized_tx_id:
                continue
            append_report_path = data_dir / "append_reports" / f"{height}.json"
            if append_report_path.is_file():
                report_obj = dict(_load_json_object(append_report_path))
            else:
                _body_path, receipts_path = _ledger_body_and_receipts_paths_v0(data_dir=data_dir, height=height)
                receipts = json.loads(receipts_path.read_text(encoding="utf-8"))
                report_obj = {
                    "schema": NODE_APPEND_REPORT_SCHEMA,
                    "ok": True,
                    "status": "accepted",
                    "height": height,
                    "tx_hash": tx_hash_v0(dict(existing_tx_raw)),
                    "body_path": str(path),
                    "receipts_path": str(receipts_path),
                    "receipt": receipts[0] if isinstance(receipts, list) and receipts else None,
                }
            report_obj["idempotent_replay"] = True
            return dict(existing_tx_raw), report_obj
    return None


def _iter_tx_operations_v0(tx: Mapping[str, Any]) -> list[Mapping[str, Any]]:
    operations = tx.get("operations")
    if not isinstance(operations, Mapping):
        return []
    out: list[Mapping[str, Any]] = []
    for raw_ops in operations.values():
        if isinstance(raw_ops, list):
            for op in raw_ops:
                if isinstance(op, Mapping):
                    out.append(op)
        elif isinstance(raw_ops, Mapping):
            out.append(raw_ops)
    return out


def _operation_module_v0(op: Mapping[str, Any]) -> str:
    return str(op.get("module", "")).strip()


def _operation_action_v0(op: Mapping[str, Any]) -> str:
    raw_kind = op.get("kind")
    if isinstance(raw_kind, str) and raw_kind.strip():
        return raw_kind.strip().upper()
    raw_action = op.get("action")
    if isinstance(raw_action, str) and raw_action.strip():
        return raw_action.strip().lower()
    return ""


def _eligible_reward_receipt_kinds_for_source_tx_v0(
    *,
    tx: Mapping[str, Any],
    recipient_pubkey: str,
) -> set[str]:
    eligible: set[str] = set()
    recipient = canonical_hex_fixed_allow_0x(recipient_pubkey, nbytes=48, name="recipient_pubkey")
    for op in _iter_tx_operations_v0(tx):
        sender = op.get("sender_pubkey", tx.get("tx_sender_pubkey"))
        module = _operation_module_v0(op)
        op_recipient = op.get(
            "recipient",
            op.get(
                "to_pubkey",
                op.get("account_pubkey", op.get("owner_pubkey", sender)),
            ),
        )
        participants = {
            str(value or "")
            for value in (
                sender,
                op_recipient,
                op.get("account_pubkey"),
                op.get("owner_pubkey"),
                op.get("to_pubkey"),
                op.get("recipient_pubkey"),
            )
        }
        if recipient not in participants:
            continue
        action = _operation_action_v0(op)
        if action == "ADD_LIQUIDITY":
            eligible.add("add_liquidity")
            eligible.add("lp_position_snapshot")
        elif action == "REMOVE_LIQUIDITY":
            eligible.add("remove_liquidity")
            eligible.add("lp_position_snapshot")
        elif action in {"ORACLE_REPORT", "oracle_report"}:
            eligible.add("oracle_report")
        elif module == "TauPerp" and action in {
            "deposit_collateral",
            "open_position",
            "close_position",
            "settle_epoch",
        }:
            eligible.add("perps_position_activity")
        elif module == "ZUSDFinance" and action == "deposit_sp":
            eligible.add("stability_pool_deposit")
            eligible.add("stability_pool_epoch_snapshot")
        elif module == "ZUSDFinance" and action in {
            "deposit_collateral",
            "withdraw_collateral",
            "mint_zusd",
            "repay_zusd",
            "redeem_zusd",
            "liquidate",
        }:
            eligible.add("zusd_vault_activity")
        elif module == "ZenoProofMining" and action == "submit_proof":
            eligible.add("proof_mining_claim")
            eligible.add("verified_proof_work")
    return eligible


def _candidate_reward_participants_for_source_tx_v0(tx: Mapping[str, Any]) -> set[str]:
    participants: set[str] = set()
    for op in _iter_tx_operations_v0(tx):
        for raw in (
            op.get("sender_pubkey", tx.get("tx_sender_pubkey")),
            op.get("recipient", op.get("sender_pubkey")),
            op.get("to_pubkey"),
            op.get("account_pubkey"),
            op.get("owner_pubkey"),
            op.get("recipient_pubkey"),
        ):
            if not isinstance(raw, str) or not raw:
                continue
            try:
                participants.add(canonical_hex_fixed_allow_0x(raw, nbytes=48, name="participant"))
            except Exception:
                continue
    return participants


def _find_latest_unclaimed_reward_source_v0(
    *,
    data_dir: Path,
    program: Mapping[str, Any],
    recipient_pubkey: str | None,
    requested_receipt_kind: str | None,
    claimed_keys: set[str],
    max_height: int,
) -> dict[str, Any]:
    eligible_for_program = set(program.get("eligibility_receipts", []))
    if not eligible_for_program:
        raise ValueError("program_has_no_eligibility_receipts")
    recipient_filter = (
        canonical_hex_fixed_allow_0x(recipient_pubkey, nbytes=48, name="recipient_pubkey")
        if recipient_pubkey
        else None
    )
    requested_kind = _require_str_token_v0(requested_receipt_kind, name="receipt_kind") if requested_receipt_kind else None
    for height in range(max_height, 0, -1):
        body_path, receipts_path = _ledger_body_and_receipts_paths_v0(data_dir=data_dir, height=height)
        if not receipts_path.is_file() or not body_path.is_file():
            continue
        receipts = json.loads(receipts_path.read_text(encoding="utf-8"))
        body = _load_json_object(body_path)
        txs = body.get("transactions")
        if not isinstance(receipts, list) or not isinstance(txs, list):
            continue
        for index in range(min(len(receipts), len(txs)) - 1, -1, -1):
            receipt = receipts[index]
            tx = txs[index]
            if not isinstance(receipt, Mapping) or not isinstance(tx, Mapping):
                continue
            if receipt.get("accepted") is not True or receipt.get("state_changed") is not True:
                continue
            receipt_hash = canonical_hex_fixed_allow_0x(receipt.get("receipt_hash"), nbytes=32, name="receipt_hash")
            tx_obj = dict(tx)
            source_tx_hash = tx_hash_v0(tx_obj)
            if receipt.get("tx_hash") != source_tx_hash:
                continue
            for participant in sorted(_candidate_reward_participants_for_source_tx_v0(tx_obj)):
                if recipient_filter is not None and participant != recipient_filter:
                    continue
                eligible = _eligible_reward_receipt_kinds_for_source_tx_v0(tx=tx_obj, recipient_pubkey=participant)
                eligible &= eligible_for_program
                if requested_kind is not None:
                    eligible &= {requested_kind}
                for receipt_kind in sorted(eligible):
                    claim_key = active_participant_reward_claim_key_v0(
                        program_id=str(program["id"]),
                        recipient_pubkey=participant,
                        receipt_hash=receipt_hash,
                    )
                    if claim_key in claimed_keys:
                        continue
                    return {
                        "receipt": dict(receipt),
                        "receipt_hash": receipt_hash,
                        "receipt_kind": receipt_kind,
                        "source_tx_hash": source_tx_hash,
                        "source_tx": tx_obj,
                        "source_height": height,
                        "source_tx_index": index,
                        "recipient_pubkey": participant,
                    }
    raise ValueError("unclaimed_reward_source_not_found")


def _source_receipt_for_tokenomics_claim_v0(
    *,
    data_dir: Path,
    source_height: int,
    source_tx_index: int,
    recipient_pubkey: str,
    requested_receipt_hash: str | None,
    requested_receipt_kind: str | None,
    max_source_height: int,
) -> dict[str, Any]:
    height = _ui_amount_int_v0(source_height, name="source_height", maximum=9_223_372_036_854_775_807)
    tx_index = _ui_amount_int_v0(source_tx_index, name="source_tx_index", maximum=1_000_000, allow_zero=True)
    if height > max_source_height:
        raise ValueError("source_height_not_yet_available")
    body_path, receipts_path = _ledger_body_and_receipts_paths_v0(data_dir=data_dir, height=height)
    # Paths come from bounded-height construction in _ledger_body_and_receipts_paths_v0.
    if not _artifact_is_file_v0(receipts_path) or not _artifact_is_file_v0(body_path):
        raise ValueError("source_receipt_not_found")
    # receipts_path is a local ledger artifact path derived from the bounded source height.
    receipts = json.loads(_read_artifact_text_v0(receipts_path))
    if not isinstance(receipts, list) or tx_index >= len(receipts) or not isinstance(receipts[tx_index], Mapping):
        raise ValueError("source_receipt_index_not_found")
    receipt = dict(receipts[tx_index])
    if receipt.get("accepted") is not True or receipt.get("state_changed") is not True:
        raise ValueError("source_receipt_not_accepted_state_change")
    receipt_hash = canonical_hex_fixed_allow_0x(receipt.get("receipt_hash"), nbytes=32, name="source_receipt.receipt_hash")
    if requested_receipt_hash is not None:
        requested_hash = canonical_hex_fixed_allow_0x(requested_receipt_hash, nbytes=32, name="receipt_hash")
        if requested_hash != receipt_hash:
            raise ValueError("source_receipt_hash_mismatch")
    body = _load_json_object(body_path)
    txs = body.get("transactions")
    if not isinstance(txs, list) or tx_index >= len(txs) or not isinstance(txs[tx_index], Mapping):
        raise ValueError("source_transaction_index_not_found")
    tx = dict(txs[tx_index])
    source_tx_hash = tx_hash_v0(tx)
    if receipt.get("tx_hash") != source_tx_hash:
        raise ValueError("source_receipt_tx_hash_mismatch")
    eligible_kinds = _eligible_reward_receipt_kinds_for_source_tx_v0(tx=tx, recipient_pubkey=recipient_pubkey)
    if requested_receipt_kind is not None:
        receipt_kind = _require_str_token_v0(requested_receipt_kind, name="receipt_kind")
        if receipt_kind not in eligible_kinds:
            raise ValueError("source_receipt_kind_not_eligible")
    elif eligible_kinds:
        receipt_kind = sorted(eligible_kinds)[0]
    else:
        raise ValueError("source_transaction_not_reward_eligible")
    return {
        "receipt": receipt,
        "receipt_hash": receipt_hash,
        "receipt_kind": receipt_kind,
        "source_tx_hash": source_tx_hash,
        "source_tx": tx,
    }


def _require_str_token_v0(value: object, *, name: str) -> str:
    if not isinstance(value, str) or not value:
        raise ValueError(f"{name} must be a non-empty string")
    return value


def _ui_tokenomics_reward_claim_tx_v0(
    *,
    data_dir: Path,
    node_status: Mapping[str, Any],
    payload: Mapping[str, Any],
    time_ms: int,
) -> dict[str, Any]:
    distribution = node_status.get("token_distribution")
    if not isinstance(distribution, Mapping) or not distribution:
        raise ValueError("token_distribution_missing")
    distribution_obj = dict(distribution)
    validate_protocol_token_distribution_v0(distribution_obj)
    latest_height, snapshot = _latest_snapshot_for_ui_v0(
        data_dir=data_dir,
        node_status=node_status,
        use_reader_lock=False,
    )
    program_id = _require_str_token_v0(payload.get("program_id", payload.get("programId")), name="program_id")
    program = active_participant_program_by_id_v0(distribution_obj, program_id)
    recipient_raw = payload.get("recipient_pubkey", payload.get("recipientPubkey", payload.get("recipient")))
    recipient = (
        _require_pubkey_v0(recipient_raw, name="recipient_pubkey")
        if isinstance(recipient_raw, str) and recipient_raw.strip()
        else None
    )
    amount_raw = payload.get("amount")
    amount = int(program["claim_amount"])
    if amount_raw is not None:
        requested_amount = _ui_amount_int_v0(
            amount_raw,
            name="amount",
            maximum=MAX_LOCAL_TESTNET_ACTIVE_PARTICIPANT_CLAIM_AMOUNT,
        )
        if requested_amount != amount:
            raise ValueError("amount_must_match_program_claim_amount")
    requested_receipt_hash_raw = payload.get("receipt_hash", payload.get("receiptHash"))
    requested_receipt_hash = requested_receipt_hash_raw if isinstance(requested_receipt_hash_raw, str) and requested_receipt_hash_raw else None
    requested_receipt_kind_raw = payload.get("receipt_kind", payload.get("receiptKind"))
    requested_receipt_kind = requested_receipt_kind_raw if isinstance(requested_receipt_kind_raw, str) and requested_receipt_kind_raw else None
    token_asset_id = str(distribution_obj["token_asset_id"])
    _circulating_supply, balances_by_pubkey = _token_balance_sum_from_snapshot_v0(snapshot, asset_id=token_asset_id)
    controller = str(program["controller_pubkey"])
    spent_by_program, claimed_keys = _tokenomics_claim_index_from_live_bodies_v0(data_dir=data_dir, max_height=latest_height)
    source_height_raw = payload.get("source_height", payload.get("sourceHeight"))
    if source_height_raw is None:
        if requested_receipt_hash is not None:
            raise ValueError("source_height_required_when_receipt_hash_is_supplied")
        source = _find_latest_unclaimed_reward_source_v0(
            data_dir=data_dir,
            program=program,
            recipient_pubkey=recipient,
            requested_receipt_kind=requested_receipt_kind,
            claimed_keys=claimed_keys,
            max_height=latest_height,
        )
        source_height = int(source["source_height"])
        source_tx_index = int(source["source_tx_index"])
        recipient = str(source["recipient_pubkey"])
    else:
        if recipient is None:
            raise ValueError("recipient_pubkey_required_for_explicit_source_height")
        source_height = _ui_amount_int_v0(
            source_height_raw,
            name="source_height",
            maximum=9_223_372_036_854_775_807,
        )
        source_tx_index = _ui_amount_int_v0(
            payload.get("source_tx_index", payload.get("sourceTxIndex", 0)),
            name="source_tx_index",
            maximum=1_000_000,
            allow_zero=True,
        )
        source = _source_receipt_for_tokenomics_claim_v0(
            data_dir=data_dir,
            source_height=source_height,
            source_tx_index=source_tx_index,
            recipient_pubkey=recipient,
            requested_receipt_hash=requested_receipt_hash,
            requested_receipt_kind=requested_receipt_kind,
            max_source_height=latest_height,
        )
    if recipient is None:
        raise ValueError("recipient_pubkey_missing")
    claim = build_active_participant_reward_claim_v0(
        distribution=distribution_obj,
        program_id=program_id,
        recipient_pubkey=recipient,
        receipt_kind=str(source["receipt_kind"]),
        receipt_hash=str(source["receipt_hash"]),
        amount=amount,
        source_height=source_height,
        source_tx_index=source_tx_index,
        source_tx_hash=str(source["source_tx_hash"]),
        spent_by_program=spent_by_program,
        claimed_keys=claimed_keys,
        reward_source_balance=int(balances_by_pubkey.get(controller, 0)),
        production_security_claim=False,
    )
    tx_id_raw = payload.get("tx_id", payload.get("txId"))
    tx_id = (
        str(tx_id_raw).strip()
        if isinstance(tx_id_raw, str) and tx_id_raw.strip()
        else f"ui-tokenomics-claim-{latest_height + 1}-{claim['claim_key'][:18]}"
    )
    return {
        "tx_id": tx_id,
        "kind": TOKENOMICS_REWARD_CLAIM_KIND,
        "block_timestamp": time_ms // 1000,
        "tx_sender_pubkey": recipient,
        "claim": claim,
    }


def _validate_tokenomics_claim_idempotent_payload_v0(
    *,
    payload: Mapping[str, Any],
    existing_tx: Mapping[str, Any],
) -> None:
    if existing_tx.get("kind") != TOKENOMICS_REWARD_CLAIM_KIND:
        raise ValueError("duplicate_tx_id_payload_mismatch")
    claim = existing_tx.get("claim")
    if not isinstance(claim, Mapping):
        raise ValueError("duplicate_tx_id_payload_mismatch")

    def _reject_if_supplied_mismatch(raw: object, expected: object, *, canonical_pubkey: bool = False) -> None:
        if raw is None:
            return
        if canonical_pubkey:
            actual_value = _require_pubkey_v0(raw, name="recipient_pubkey")
            expected_value = _require_pubkey_v0(expected, name="claim.recipient_pubkey")
        else:
            actual_value = str(raw)
            expected_value = str(expected)
        if actual_value != expected_value:
            raise ValueError("duplicate_tx_id_payload_mismatch")

    _reject_if_supplied_mismatch(payload.get("program_id", payload.get("programId")), claim.get("program_id"))
    _reject_if_supplied_mismatch(
        payload.get("recipient_pubkey", payload.get("recipientPubkey", payload.get("recipient"))),
        claim.get("recipient_pubkey"),
        canonical_pubkey=True,
    )
    _reject_if_supplied_mismatch(payload.get("receipt_hash", payload.get("receiptHash")), claim.get("receipt_hash"))
    _reject_if_supplied_mismatch(payload.get("receipt_kind", payload.get("receiptKind")), claim.get("receipt_kind"))
    amount_raw = payload.get("amount")
    if amount_raw is not None and _ui_amount_int_v0(
        amount_raw,
        name="amount",
        maximum=MAX_LOCAL_TESTNET_ACTIVE_PARTICIPANT_CLAIM_AMOUNT,
    ) != int(claim.get("amount", -1)):
        raise ValueError("duplicate_tx_id_payload_mismatch")
    source_height_raw = payload.get("source_height", payload.get("sourceHeight"))
    if source_height_raw is not None and _ui_amount_int_v0(
        source_height_raw,
        name="source_height",
        maximum=9_223_372_036_854_775_807,
    ) != int(claim.get("source_height", -1)):
        raise ValueError("duplicate_tx_id_payload_mismatch")
    source_tx_index_raw = payload.get("source_tx_index", payload.get("sourceTxIndex"))
    if source_tx_index_raw is not None and _ui_amount_int_v0(
        source_tx_index_raw,
        name="source_tx_index",
        maximum=1_000_000,
        allow_zero=True,
    ) != int(claim.get("source_tx_index", -1)):
        raise ValueError("duplicate_tx_id_payload_mismatch")


def _ui_pool_rows_from_snapshot_v0(
    *,
    snapshot: Mapping[str, Any],
    node_status: Mapping[str, Any],
    account_pubkey: str | None = None,
    analytics_by_pool: Mapping[str, Mapping[str, Any]] | None = None,
) -> list[dict[str, Any]]:
    by_asset, _by_symbol = _ui_token_catalog_v0(node_status)
    account_state = state_from_snapshot(snapshot) if account_pubkey else None
    raw_pools = snapshot.get("pools", [])
    if not isinstance(raw_pools, list):
        raise ValueError("snapshot.pools must be a list")
    rows: list[dict[str, Any]] = []
    for raw in raw_pools:
        if not isinstance(raw, Mapping):
            continue
        asset0 = _require_asset_v0(raw.get("asset0"), name="pool.asset0")
        asset1 = _require_asset_v0(raw.get("asset1"), name="pool.asset1")
        pool_id = str(raw.get("pool_id", ""))
        if pool_id == "":
            continue
        status = str(raw.get("status", "ACTIVE"))
        row = {
            "pool_id": pool_id,
            "poolId": pool_id,
            "asset0": asset0,
            "asset1": asset1,
            "token0": by_asset.get(asset0, asset0),
            "token1": by_asset.get(asset1, asset1),
            "reserve0": int(raw.get("reserve0", 0)),
            "reserve1": int(raw.get("reserve1", 0)),
            "fee_bps": int(raw.get("fee_bps", 30)),
            "feeBps": int(raw.get("fee_bps", 30)),
            "lp_supply": int(raw.get("lp_supply", 0)),
            "lpSupply": int(raw.get("lp_supply", 0)),
            "status": status,
        }
        analytics = analytics_by_pool.get(pool_id) if analytics_by_pool is not None else None
        if isinstance(analytics, Mapping):
            swap_count_24h = int(analytics.get("swap_count_24h", 0))
            volume_by_asset = analytics.get("input_volume_by_asset_24h")
            fee_by_asset = analytics.get("fee_by_asset_24h")
            input_volume0_24h = (
                int(volume_by_asset.get(asset0, 0))
                if isinstance(volume_by_asset, Mapping)
                else int(analytics.get("input_volume0_24h", 0))
            )
            input_volume1_24h = (
                int(volume_by_asset.get(asset1, 0))
                if isinstance(volume_by_asset, Mapping)
                else int(analytics.get("input_volume1_24h", 0))
            )
            fee0_24h = (
                int(fee_by_asset.get(asset0, 0))
                if isinstance(fee_by_asset, Mapping)
                else int(analytics.get("fee0_24h", 0))
            )
            fee1_24h = (
                int(fee_by_asset.get(asset1, 0))
                if isinstance(fee_by_asset, Mapping)
                else int(analytics.get("fee1_24h", 0))
            )
            row.update(
                {
                    "swap_count_24h": swap_count_24h,
                    "swapCount24h": swap_count_24h,
                    "input_volume0_24h": input_volume0_24h,
                    "inputVolume0_24h": input_volume0_24h,
                    "input_volume1_24h": input_volume1_24h,
                    "inputVolume1_24h": input_volume1_24h,
                    "fee0_24h": fee0_24h,
                    "fee0_24h_units": fee0_24h,
                    "fee0_24hUnits": fee0_24h,
                    "fee1_24h": fee1_24h,
                    "fee1_24h_units": fee1_24h,
                    "fee1_24hUnits": fee1_24h,
                }
            )
        if account_state is not None and account_pubkey is not None:
            row.update(
                {
                    "account": account_pubkey,
                    "account_lp_balance": int(account_state.lp_balances.get(account_pubkey, pool_id)),
                    "accountLpBalance": int(account_state.lp_balances.get(account_pubkey, pool_id)),
                    "account_balance0": int(account_state.balances.get(account_pubkey, asset0)),
                    "accountBalance0": int(account_state.balances.get(account_pubkey, asset0)),
                    "account_balance1": int(account_state.balances.get(account_pubkey, asset1)),
                    "accountBalance1": int(account_state.balances.get(account_pubkey, asset1)),
                }
            )
        rows.append(row)
    return rows


def _ui_pools_response_v0(
    *,
    data_dir: Path,
    node_status: Mapping[str, Any],
    account_pubkey: str | None = None,
) -> dict[str, Any]:
    latest_height, snapshot = _latest_snapshot_for_ui_v0(data_dir=data_dir, node_status=node_status)
    analytics_error = None
    try:
        analytics = _ui_pool_analytics_from_live_bodies_v0(data_dir=data_dir, max_height=latest_height)
    except Exception as exc:
        analytics = {"by_pool": {}, "window": None}
        analytics_error = str(exc)
    pools = _ui_pool_rows_from_snapshot_v0(
        snapshot=snapshot,
        node_status=node_status,
        account_pubkey=account_pubkey,
        analytics_by_pool=analytics.get("by_pool") if isinstance(analytics.get("by_pool"), Mapping) else {},
    )
    pool_assets = {
        str(pool[asset_key])
        for pool in pools
        for asset_key in ("asset0", "asset1")
        if isinstance(pool.get(asset_key), str)
    }
    by_asset, _by_symbol = _ui_token_catalog_v0(node_status)
    tokens = [
        {"symbol": symbol, "asset_id": asset, "in_pool": asset in pool_assets}
        for asset, symbol in sorted(by_asset.items(), key=lambda item: item[1].upper())
    ]
    response = {
        "ok": True,
        "schema": "zenodex.zeno_ledger.ui_pools.v0",
        "source": "zeno_ledger_node_live",
        "latest_height": latest_height,
        "pools": pools,
        "tokens": tokens,
        "account": account_pubkey,
        "pool_analytics_window": analytics.get("window"),
    }
    if analytics_error:
        response["pool_analytics_error"] = analytics_error
    if account_pubkey:
        response["account_last_nonce"] = _snapshot_last_nonce_v0(snapshot, account_pubkey)
    return response


def _snapshot_last_nonce_v0(snapshot: Mapping[str, Any], pubkey: str) -> int:
    raw_nonces = snapshot.get("nonces", [])
    if not isinstance(raw_nonces, list):
        return 0
    for row in raw_nonces:
        if not isinstance(row, Mapping):
            continue
        if row.get("pubkey") == pubkey:
            raw_last = row.get("last_nonce", 0)
            if isinstance(raw_last, int) and not isinstance(raw_last, bool) and raw_last >= 0:
                return raw_last
    return 0


def _asset_from_ui_symbol_v0(
    raw: object,
    *,
    by_symbol: Mapping[str, Mapping[str, str]],
    name: str,
) -> str:
    if not isinstance(raw, str) or raw.strip() == "":
        raise ValueError(f"{name} is required")
    text = raw.strip()
    try:
        return _require_asset_v0(text, name=name)
    except Exception:
        token = by_symbol.get(text.upper())
        if token and isinstance(token.get("asset_id"), str):
            return token["asset_id"]
    raise ValueError(f"{name} does not match a testnet token")


def _find_ui_swap_pool_v0(
    *,
    snapshot: Mapping[str, Any],
    node_status: Mapping[str, Any],
    payload: Mapping[str, Any],
) -> tuple[Mapping[str, Any], str, str]:
    _by_asset, by_symbol = _ui_token_catalog_v0(node_status)
    raw_pools = snapshot.get("pools", [])
    if not isinstance(raw_pools, list):
        raise ValueError("snapshot.pools must be a list")
    pool_id_hint = payload.get("pool_id", payload.get("poolId"))
    requested_pool_id = pool_id_hint if isinstance(pool_id_hint, str) and pool_id_hint.strip() else None
    asset_in_raw = payload.get("asset_in", payload.get("assetIn", payload.get("from")))
    asset_out_raw = payload.get("asset_out", payload.get("assetOut", payload.get("to")))
    asset_in = _asset_from_ui_symbol_v0(asset_in_raw, by_symbol=by_symbol, name="asset_in")
    asset_out = _asset_from_ui_symbol_v0(asset_out_raw, by_symbol=by_symbol, name="asset_out")
    if asset_in == asset_out:
        raise ValueError("asset_in and asset_out must differ")

    for row in raw_pools:
        if not isinstance(row, Mapping):
            continue
        row_pool_id = str(row.get("pool_id", ""))
        if requested_pool_id is not None and row_pool_id != requested_pool_id:
            continue
        row_asset0 = _require_asset_v0(row.get("asset0"), name="pool.asset0")
        row_asset1 = _require_asset_v0(row.get("asset1"), name="pool.asset1")
        if {row_asset0, row_asset1} == {asset_in, asset_out}:
            if str(row.get("status", "ACTIVE")) != "ACTIVE":
                raise ValueError("pool is not active")
            return row, asset_in, asset_out
    raise ValueError("matching pool not found")


def _find_ui_liquidity_pool_v0(
    *,
    snapshot: Mapping[str, Any],
    node_status: Mapping[str, Any],
    payload: Mapping[str, Any],
) -> tuple[Mapping[str, Any], str]:
    _by_asset, by_symbol = _ui_token_catalog_v0(node_status)
    raw_pools = snapshot.get("pools", [])
    if not isinstance(raw_pools, list):
        raise ValueError("snapshot.pools must be a list")
    pool_id_hint = payload.get("pool_id", payload.get("poolId", payload.get("id")))
    requested_pool_id = pool_id_hint if isinstance(pool_id_hint, str) and pool_id_hint.strip() else None
    asset0_raw = payload.get("asset0", payload.get("token0"))
    asset1_raw = payload.get("asset1", payload.get("token1"))
    asset0 = _asset_from_ui_symbol_v0(asset0_raw, by_symbol=by_symbol, name="asset0") if asset0_raw is not None else None
    asset1 = _asset_from_ui_symbol_v0(asset1_raw, by_symbol=by_symbol, name="asset1") if asset1_raw is not None else None

    for row in raw_pools:
        if not isinstance(row, Mapping):
            continue
        row_pool_id = str(row.get("pool_id", ""))
        if requested_pool_id is not None and row_pool_id != requested_pool_id:
            continue
        row_asset0 = _require_asset_v0(row.get("asset0"), name="pool.asset0")
        row_asset1 = _require_asset_v0(row.get("asset1"), name="pool.asset1")
        if asset0 is not None and asset1 is not None and {row_asset0, row_asset1} != {asset0, asset1}:
            continue
        if str(row.get("status", "ACTIVE")) != "ACTIVE":
            raise ValueError("pool is not active")
        return row, row_pool_id
    raise ValueError("matching pool not found")


def _ui_swap_tx_v0(
    *,
    data_dir: Path,
    node_status: Mapping[str, Any],
    payload: Mapping[str, Any],
    time_ms: int,
) -> dict[str, Any]:
    sender_raw = payload.get("sender_pubkey", payload.get("senderPubkey", payload.get("sender")))
    recipient_raw = payload.get("recipient", sender_raw)
    sender = _require_pubkey_v0(sender_raw, name="sender_pubkey")
    recipient = _require_pubkey_v0(recipient_raw, name="recipient")
    amount_in = _ui_amount_int_v0(
        payload.get("amount_in", payload.get("amountIn")),
        name="amount_in",
        maximum=MAX_TESTNET_FAUCET_AMOUNT,
    )
    min_amount_out = _ui_amount_int_v0(
        payload.get("min_amount_out", payload.get("minAmountOut", 1)),
        name="min_amount_out",
        maximum=MAX_TESTNET_FAUCET_AMOUNT,
        allow_zero=True,
    )
    deadline = _ui_amount_int_v0(
        payload.get("deadline", 1_999_999_999),
        name="deadline",
        maximum=9_999_999_999,
    )
    latest_height, snapshot = _latest_snapshot_for_ui_v0(data_dir=data_dir, node_status=node_status)
    pool, asset_in, asset_out = _find_ui_swap_pool_v0(snapshot=snapshot, node_status=node_status, payload=payload)
    pre_state = state_from_snapshot(snapshot)
    if pre_state.balances.get(sender, asset_in) < amount_in:
        raise ValueError("balance_insufficient")
    pool_asset0 = _require_asset_v0(pool.get("asset0"), name="pool.asset0")
    reserve0 = _ui_amount_int_v0(pool.get("reserve0"), name="pool.reserve0", maximum=10**30)
    reserve1 = _ui_amount_int_v0(pool.get("reserve1"), name="pool.reserve1", maximum=10**30)
    fee_bps = _ui_amount_int_v0(pool.get("fee_bps", pool.get("feeBps", 0)), name="pool.fee_bps", maximum=10_000, allow_zero=True)
    if asset_in == pool_asset0:
        reserve_in, reserve_out = reserve0, reserve1
    else:
        reserve_in, reserve_out = reserve1, reserve0
    if reserve_in <= 0 or reserve_out <= 0:
        raise ValueError("pool reserves must be positive")
    amount_in_less_fee = amount_in * (10_000 - fee_bps)
    quoted_amount_out = (reserve_out * amount_in_less_fee) // (reserve_in * 10_000 + amount_in_less_fee)
    if quoted_amount_out <= 0:
        raise ValueError("amount_out_zero")
    if quoted_amount_out < min_amount_out:
        raise ValueError("slippage_min_amount_out")
    nonce_raw = payload.get("nonce")
    if nonce_raw is None:
        nonce = _snapshot_last_nonce_v0(snapshot, sender) + 1
    else:
        nonce = _ui_amount_int_v0(nonce_raw, name="nonce", maximum=9_223_372_036_854_775_807)
    pool_id = str(pool["pool_id"])
    signature = _optional_intent_signature_v0(payload)
    intent_payload = {
        "sender_pubkey": sender,
        "recipient": recipient,
        "pool_id": pool_id,
        "asset_in": asset_in,
        "asset_out": asset_out,
        "amount_in": amount_in,
        "min_amount_out": min_amount_out,
        "nonce": nonce,
    }
    tx_id_raw = payload.get("tx_id", payload.get("txId"))
    tx_id = (
        str(tx_id_raw).strip()
        if isinstance(tx_id_raw, str) and tx_id_raw.strip()
        else _default_ui_intent_tx_id_v0(
            prefix="ui-swap",
            sender=sender,
            nonce=nonce,
            intent_payload=intent_payload,
        )
    )
    operation: dict[str, Any] = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "SWAP_EXACT_IN",
        "intent_id": hash_v0("ui_swap_intent_v0", intent_payload),
        "sender_pubkey": sender,
        "deadline": deadline,
        "nonce": nonce,
        "pool_id": pool_id,
        "asset_in": asset_in,
        "asset_out": asset_out,
        "amount_in": amount_in,
        "min_amount_out": min_amount_out,
        "recipient": recipient,
    }
    if signature is not None:
        operation["signature"] = signature
    return {
        "tx_id": tx_id,
        "block_timestamp": time_ms // 1000,
        "tx_sender_pubkey": sender,
        "operations": {"5": [operation]},
    }


def _ui_liquidity_tx_v0(
    *,
    data_dir: Path,
    node_status: Mapping[str, Any],
    payload: Mapping[str, Any],
    time_ms: int,
    kind: str,
    min_lp_position_age_seconds: int = 0,
    lp_duration_risk_policy: Any | None = None,
) -> dict[str, Any]:
    if kind not in {"ADD_LIQUIDITY", "REMOVE_LIQUIDITY"}:
        raise ValueError(f"unsupported liquidity kind: {kind}")
    sender_raw = payload.get("sender_pubkey", payload.get("senderPubkey", payload.get("sender")))
    recipient_raw = payload.get("recipient", sender_raw)
    sender = _require_pubkey_v0(sender_raw, name="sender_pubkey")
    recipient = _require_pubkey_v0(recipient_raw, name="recipient")
    deadline = _ui_amount_int_v0(
        payload.get("deadline", 1_999_999_999),
        name="deadline",
        maximum=9_999_999_999,
    )
    latest_height, snapshot = _latest_snapshot_for_ui_v0(data_dir=data_dir, node_status=node_status)
    pool, pool_id = _find_ui_liquidity_pool_v0(snapshot=snapshot, node_status=node_status, payload=payload)
    pre_state = state_from_snapshot(snapshot)
    pool_state = pre_state.pools.get(pool_id)
    if pool_state is None:
        raise ValueError("matching pool not found")

    amount0_min = _ui_amount_int_v0(
        payload.get("amount0_min", payload.get("amount0Min", 0)),
        name="amount0_min",
        maximum=MAX_TESTNET_FAUCET_AMOUNT,
        allow_zero=True,
    )
    amount1_min = _ui_amount_int_v0(
        payload.get("amount1_min", payload.get("amount1Min", 0)),
        name="amount1_min",
        maximum=MAX_TESTNET_FAUCET_AMOUNT,
        allow_zero=True,
    )
    intent_payload: dict[str, Any] = {
        "sender_pubkey": sender,
        "recipient": recipient,
        "pool_id": pool_id,
        "amount0_min": amount0_min,
        "amount1_min": amount1_min,
    }
    operation: dict[str, Any] = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": kind,
        "sender_pubkey": sender,
        "deadline": deadline,
        "pool_id": pool_id,
        "amount0_min": amount0_min,
        "amount1_min": amount1_min,
        "recipient": recipient,
    }

    if kind == "ADD_LIQUIDITY":
        amount0_desired = _ui_amount_int_v0(
            payload.get("amount0_desired", payload.get("amount0Desired", payload.get("amount0"))),
            name="amount0_desired",
            maximum=MAX_TESTNET_FAUCET_AMOUNT,
        )
        amount1_desired = _ui_amount_int_v0(
            payload.get("amount1_desired", payload.get("amount1Desired", payload.get("amount1"))),
            name="amount1_desired",
            maximum=MAX_TESTNET_FAUCET_AMOUNT,
        )
        from src.core.liquidity import add_liquidity  # pylint: disable=import-outside-toplevel

        amount0_used, amount1_used, lp_minted = add_liquidity(
            pool_state=pool_state,
            amount0_desired=amount0_desired,
            amount1_desired=amount1_desired,
            amount0_min=amount0_min,
            amount1_min=amount1_min,
        )
        if pre_state.balances.get(sender, pool_state.asset0) < amount0_used:
            raise ValueError("balance_insufficient")
        if pre_state.balances.get(sender, pool_state.asset1) < amount1_used:
            raise ValueError("balance_insufficient")
        operation.update(
            {
                "amount0_desired": amount0_desired,
                "amount1_desired": amount1_desired,
            }
        )
        intent_payload.update(
            {
                "amount0_desired": amount0_desired,
                "amount1_desired": amount1_desired,
                "amount0_used": amount0_used,
                "amount1_used": amount1_used,
                "lp_minted": lp_minted,
            }
        )
    else:
        lp_amount = _ui_amount_int_v0(
            payload.get("lp_amount", payload.get("lpAmount")),
            name="lp_amount",
            maximum=MAX_TESTNET_FAUCET_AMOUNT,
        )
        if pre_state.lp_balances.get(sender, pool_id) < lp_amount:
            raise ValueError("lp_balance_insufficient")
        if min_lp_position_age_seconds > 0 or lp_duration_risk_policy is not None:
            from src.integration.lp_position_age_gate import (  # pylint: disable=import-outside-toplevel
                effective_lp_position_age_seconds,
            )

            block_timestamp = time_ms // 1000
            last_mint = pre_state.lp_balances.get_last_mint_timestamp(sender, pool_id)
            if last_mint is None:
                raise ValueError("lp_position_age_missing")
            if last_mint > block_timestamp:
                raise ValueError("lp_position_mint_timestamp_in_future")
            required_age = effective_lp_position_age_seconds(
                lp_balances=pre_state.lp_balances,
                owner=sender,
                pool_id=pool_id,
                block_timestamp=block_timestamp,
                min_lp_position_age_seconds=min_lp_position_age_seconds,
                duration_risk_policy=lp_duration_risk_policy,
            )
            actual_age = block_timestamp - int(last_mint)
            if actual_age < required_age:
                raise ValueError(f"lp_position_locked:{actual_age}<{required_age}")
        from src.core.liquidity import remove_liquidity  # pylint: disable=import-outside-toplevel

        amount0_out, amount1_out = remove_liquidity(
            pool_state=pool_state,
            lp_amount=lp_amount,
            amount0_min=amount0_min,
            amount1_min=amount1_min,
        )
        operation.update({"lp_amount": lp_amount})
        intent_payload.update(
            {
                "lp_amount": lp_amount,
                "amount0_out": amount0_out,
                "amount1_out": amount1_out,
            }
        )

    nonce_raw = payload.get("nonce")
    if nonce_raw is None:
        nonce = _snapshot_last_nonce_v0(snapshot, sender) + 1
    else:
        nonce = _ui_amount_int_v0(nonce_raw, name="nonce", maximum=9_223_372_036_854_775_807)
    operation["nonce"] = nonce
    intent_payload["nonce"] = nonce
    tx_id_raw = payload.get("tx_id", payload.get("txId"))
    default_prefix = "ui-add-liquidity" if kind == "ADD_LIQUIDITY" else "ui-remove-liquidity"
    tx_id = (
        str(tx_id_raw).strip()
        if isinstance(tx_id_raw, str) and tx_id_raw.strip()
        else _default_ui_intent_tx_id_v0(
            prefix=default_prefix,
            sender=sender,
            nonce=nonce,
            intent_payload=intent_payload,
        )
    )
    operation["intent_id"] = hash_v0(f"{default_prefix}_intent_v0", intent_payload)
    signature = _optional_intent_signature_v0(payload)
    if signature is not None:
        operation["signature"] = signature
    return {
        "tx_id": tx_id,
        "block_timestamp": time_ms // 1000,
        "tx_sender_pubkey": sender,
        "operations": {"5": [operation]},
    }


def _ui_create_pool_tx_v0(
    *,
    data_dir: Path,
    node_status: Mapping[str, Any],
    payload: Mapping[str, Any],
    time_ms: int,
) -> dict[str, Any]:
    _by_asset, by_symbol = _ui_token_catalog_v0(node_status)
    sender_raw = payload.get("sender_pubkey", payload.get("senderPubkey", payload.get("sender")))
    sender = _require_pubkey_v0(sender_raw, name="sender_pubkey")
    deadline = _ui_amount_int_v0(
        payload.get("deadline", 1_999_999_999),
        name="deadline",
        maximum=9_999_999_999,
    )
    raw_asset0 = _asset_from_ui_symbol_v0(
        payload.get("asset0", payload.get("token0", payload.get("assetA"))),
        by_symbol=by_symbol,
        name="asset0",
    )
    raw_asset1 = _asset_from_ui_symbol_v0(
        payload.get("asset1", payload.get("token1", payload.get("assetB"))),
        by_symbol=by_symbol,
        name="asset1",
    )
    if raw_asset0 == raw_asset1:
        raise ValueError("asset0 and asset1 must differ")
    raw_amount0 = _ui_amount_int_v0(
        payload.get("amount0", payload.get("amount0Desired", payload.get("amountA"))),
        name="amount0",
        maximum=MAX_TESTNET_FAUCET_AMOUNT,
    )
    raw_amount1 = _ui_amount_int_v0(
        payload.get("amount1", payload.get("amount1Desired", payload.get("amountB"))),
        name="amount1",
        maximum=MAX_TESTNET_FAUCET_AMOUNT,
    )
    fee_bps = _ui_amount_int_v0(
        payload.get("fee_bps", payload.get("feeBps", 30)),
        name="fee_bps",
        maximum=10_000,
        allow_zero=True,
    )
    created_at = _ui_amount_int_v0(
        payload.get("created_at", payload.get("createdAt", time_ms // 1000)),
        name="created_at",
        maximum=9_999_999_999,
        allow_zero=True,
    )
    if raw_asset0 < raw_asset1:
        asset0, asset1 = raw_asset0, raw_asset1
        amount0, amount1 = raw_amount0, raw_amount1
    else:
        asset0, asset1 = raw_asset1, raw_asset0
        amount0, amount1 = raw_amount1, raw_amount0

    latest_height, snapshot = _latest_snapshot_for_ui_v0(data_dir=data_dir, node_status=node_status)
    pool_id = compute_pool_id(asset0, asset1, fee_bps)
    pre_state = state_from_snapshot(snapshot)
    if pool_id in pre_state.pools:
        raise ValueError("pool_already_exists")
    if pre_state.balances.get(sender, asset0) < amount0:
        raise ValueError("balance_insufficient")
    if pre_state.balances.get(sender, asset1) < amount1:
        raise ValueError("balance_insufficient")

    nonce_raw = payload.get("nonce")
    if nonce_raw is None:
        nonce = _snapshot_last_nonce_v0(snapshot, sender) + 1
    else:
        nonce = _ui_amount_int_v0(nonce_raw, name="nonce", maximum=9_223_372_036_854_775_807)
    intent_payload = {
        "sender_pubkey": sender,
        "asset0": asset0,
        "asset1": asset1,
        "fee_bps": fee_bps,
        "amount0": amount0,
        "amount1": amount1,
        "created_at": created_at,
        "nonce": nonce,
    }
    operation: dict[str, Any] = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "CREATE_POOL",
        "intent_id": hash_v0("ui-create-pool_intent_v0", intent_payload),
        "sender_pubkey": sender,
        "deadline": deadline,
        "nonce": nonce,
        "asset0": asset0,
        "asset1": asset1,
        "fee_bps": fee_bps,
        "amount0": amount0,
        "amount1": amount1,
        "created_at": created_at,
    }
    signature = _optional_intent_signature_v0(payload)
    if signature is not None:
        operation["signature"] = signature
    tx_id_raw = payload.get("tx_id", payload.get("txId"))
    tx_id = (
        str(tx_id_raw).strip()
        if isinstance(tx_id_raw, str) and tx_id_raw.strip()
        else _default_ui_intent_tx_id_v0(
            prefix="ui-create-pool",
            sender=sender,
            nonce=nonce,
            intent_payload=intent_payload,
        )
    )
    return {
        "tx_id": tx_id,
        "block_timestamp": time_ms // 1000,
        "tx_sender_pubkey": sender,
        "operations": {"5": [operation]},
    }


def _optional_intent_signature_v0(payload: Mapping[str, Any]) -> str | None:
    raw = payload.get("signature", payload.get("intent_signature", payload.get("intentSignature")))
    if raw is None:
        return None
    if not isinstance(raw, str):
        raise ValueError("signature must be a string")
    signature = raw.strip()
    if not signature:
        raise ValueError("signature must be non-empty")
    return signature


def _local_fixture_faucet_ack_v0(payload: Mapping[str, Any]) -> bool:
    return payload.get("local_fixture_mode") is True or payload.get("localFixtureMode") is True


def _faucet_tx_v0(
    *,
    tx_id: str,
    to_pubkey: str,
    asset: str,
    amount: int,
) -> dict[str, Any]:
    return {
        "tx_id": tx_id,
        "kind": TESTNET_FAUCET_KIND,
        "to_pubkey": to_pubkey,
        "asset": asset,
        "amount": amount,
    }


def _is_faucet_body_v0(body: Mapping[str, Any]) -> bool:
    txs = body.get("transactions")
    if not isinstance(txs, list) or len(txs) != 1 or not isinstance(txs[0], Mapping):
        return False
    return txs[0].get("kind") == TESTNET_FAUCET_KIND


def _latest_live_state_path(data_dir: Path) -> Path:
    return data_dir / "live_state.json"


def _live_state_file_under_data_dir_v0(value: object, *, data_dir: Path, field: str) -> Path:
    """Resolve a live_state path field and require it to be an existing file inside data_dir.

    Relative path strings are interpreted relative to ``data_dir`` and absolute path
    strings are honoured as-is, but after resolution the target must stay strictly
    inside ``data_dir.resolve()``. Arbitrary absolute paths or ``..`` traversal that
    escape the node directory are rejected so a malicious live_state cannot point the
    node at files outside its own data directory.
    """
    if not isinstance(value, str) or value == "":
        raise ValueError(f"{field} must be a non-empty string path")
    data_root = data_dir.resolve()
    resolved = (data_root / value).resolve()
    if resolved == data_root or data_root not in resolved.parents:
        raise ValueError(f"{field} must resolve to a path inside the node data_dir")
    if not resolved.is_file():
        raise ValueError(f"{field} does not exist as a file")
    if resolved.stat().st_size > MAX_REMOTE_ARTIFACT_BYTES:
        raise ValueError(f"{field} is too large")
    return resolved


def _live_state_canonical_hash_v0(value: object, *, field: str) -> str:
    """Require a canonical 32-byte, 0x-prefixed, lowercase hex string."""
    if not isinstance(value, str):
        raise ValueError(f"{field} must be a string")
    canonical = canonical_hex_fixed_allow_0x(value, nbytes=32, name=field)
    if value != canonical:
        raise ValueError(f"{field} must be a canonical 0x-prefixed lowercase 32-byte hex string")
    return canonical


def _validate_live_state_v0(
    live_state: Mapping[str, Any],
    *,
    data_dir: Path,
    node_status: Mapping[str, Any] | None = None,
) -> None:
    """Fail closed unless every live_state field is well-formed and self-consistent."""
    if live_state.get("schema") != NODE_LIVE_STATE_SCHEMA:
        raise ValueError("live_state schema mismatch")
    for field in (
        "latest_height",
        "latest_header_path",
        "latest_snapshot_path",
        "latest_header_hash",
        "latest_app_hash",
    ):
        if field not in live_state:
            raise ValueError(f"live_state missing field: {field}")

    latest_height = live_state["latest_height"]
    if not isinstance(latest_height, int) or isinstance(latest_height, bool) or latest_height < 0:
        raise ValueError("latest_height must be a non-negative int")

    header_path = _live_state_file_under_data_dir_v0(
        live_state["latest_header_path"], data_dir=data_dir, field="latest_header_path"
    )
    snapshot_path = _live_state_file_under_data_dir_v0(
        live_state["latest_snapshot_path"], data_dir=data_dir, field="latest_snapshot_path"
    )

    header_hash = _live_state_canonical_hash_v0(live_state["latest_header_hash"], field="latest_header_hash")
    app_hash = _live_state_canonical_hash_v0(live_state["latest_app_hash"], field="latest_app_hash")

    header = dict(_load_json_object(header_path))
    if canonical_header_hash_v0(header) != header_hash:
        raise ValueError("latest_header_hash does not match latest_header_path")
    if header.get("height") != latest_height:
        raise ValueError("header height does not match latest_height")
    if node_status is not None:
        if header.get("chain_id") != node_status.get("chain_id"):
            raise ValueError("header chain_id does not match node status")
        bootstrap_height = node_status.get("latest_height")
        if not isinstance(bootstrap_height, int) or isinstance(bootstrap_height, bool) or bootstrap_height < 0:
            raise ValueError("node status latest_height must be a non-negative int")
        if latest_height < bootstrap_height:
            raise ValueError("live_state latest_height is below node status latest_height")
        if latest_height == bootstrap_height:
            if header_hash != node_status.get("last_header_hash"):
                raise ValueError("bootstrap live_state header_hash does not match node status")
            if app_hash != node_status.get("last_app_hash"):
                raise ValueError("bootstrap live_state app_hash does not match node status")
    expected_app_hash = compute_app_hash_v0(
        {
            "chain_id": header["chain_id"],
            "height": header["height"],
            "post_state_root": header["post_state_root"],
            "evidence_root": header["evidence_root"],
            "config_digest": header["config_digest"],
            "module_versions_digest": header["module_versions_digest"],
        }
    )
    if expected_app_hash != app_hash:
        raise ValueError("header app_hash does not match committed header fields")
    if header.get("app_hash") != app_hash:
        raise ValueError("header app_hash does not match latest_app_hash")
    state_file_root = _state_root_for_live_state_file_v0(snapshot_path)
    if header.get("post_state_root") != state_file_root:
        raise ValueError("latest_snapshot_path does not match header post_state_root")


def _load_live_state_v0(data_dir: Path, *, node_status: Mapping[str, Any] | None = None) -> Mapping[str, Any]:
    try:
        live_state = _load_json_object(_latest_live_state_path(data_dir))
        _validate_live_state_v0(live_state, data_dir=data_dir, node_status=node_status)
    except (OSError, json.JSONDecodeError, ValueError, TypeError) as exc:
        raise ValueError("live_state_invalid") from exc
    return live_state


def _detect_orphan_block_heights_v0(*, data_dir: Path, latest_height: int) -> list[int]:
    """Return live_ledger header heights strictly above the pointer's latest_height.

    Such heights only exist when the writer crashed between writing block
    artifacts and updating the live_state pointer. Silently overwriting them
    on the next append would erase an already-acknowledged block.
    """
    headers_dir = data_dir / "live_ledger" / "headers"
    return [h for h in _header_heights(headers_dir) if h > latest_height]


def _live_base_paths(*, bundle_root: Path, data_dir: Path, node_status: Mapping[str, Any]) -> dict[str, Any]:
    live_state_path = _latest_live_state_path(data_dir)
    if live_state_path.is_file():
        live_state = _load_live_state_v0(data_dir, node_status=node_status)
        latest_height = int(live_state["latest_height"])
        orphans = _detect_orphan_block_heights_v0(data_dir=data_dir, latest_height=latest_height)
        if orphans:
            raise ValueError(
                "orphan_blocks_above_pointer: "
                f"latest_height={latest_height} orphan_heights={orphans[:8]}"
                + (f" (+{len(orphans) - 8} more)" if len(orphans) > 8 else "")
                + " — writer likely crashed mid-append; resolve before continuing"
            )
        return {
            "latest_height": latest_height,
            "prev_header_path": _live_state_file_under_data_dir_v0(
                live_state["latest_header_path"], data_dir=data_dir, field="latest_header_path"
            ),
            "pre_snapshot_path": _live_state_file_under_data_dir_v0(
                live_state["latest_snapshot_path"], data_dir=data_dir, field="latest_snapshot_path"
            ),
        }

    latest_height = int(node_status["latest_height"])
    orphans = _detect_orphan_block_heights_v0(data_dir=data_dir, latest_height=latest_height)
    if orphans:
        raise ValueError(
            "orphan_blocks_above_pointer: "
            f"latest_height={latest_height} orphan_heights={orphans[:8]}"
            + (f" (+{len(orphans) - 8} more)" if len(orphans) > 8 else "")
            + " — writer likely crashed mid-append; resolve before continuing"
        )
    bootstrap_root = bundle_root / "bootstrap"
    return {
        "latest_height": latest_height,
        "prev_header_path": bootstrap_root / "ledger" / "headers" / f"{latest_height}.json",
        "pre_snapshot_path": bootstrap_root / "ledger" / "snapshots" / f"{latest_height}.json",
    }


@contextmanager
def _data_dir_writer_lock_v0(data_dir: Path):
    """Cross-process exclusive lock on the node's live-ledger writer surface.

    The HTTP handler's in-process ``append_lock`` does not protect against a
    second process (CLI ``append-testnet-faucet``, a sidecar pull job, an
    operator script) writing to the same data_dir concurrently. We use
    ``fcntl.flock`` on a sentinel file inside the data dir so any append or
    pull surface that calls this gets serialized at the OS level.
    """
    data_dir.mkdir(parents=True, exist_ok=True)
    lock_path = data_dir / "writer.lock"
    fd = os.open(lock_path, os.O_RDWR | os.O_CREAT, 0o600)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(fd, fcntl.LOCK_UN)
    finally:
        os.close(fd)


@contextmanager
def _data_dir_reader_lock_v0(data_dir: Path):
    """Shared lock for live-ledger readers that need a coherent pointer read."""
    data_dir.mkdir(parents=True, exist_ok=True)
    lock_path = data_dir / "writer.lock"
    fd = os.open(lock_path, os.O_RDONLY | os.O_CREAT, 0o600)
    try:
        fcntl.flock(fd, fcntl.LOCK_SH)
        try:
            yield
        finally:
            fcntl.flock(fd, fcntl.LOCK_UN)
    finally:
        os.close(fd)


def _write_live_state(
    *,
    data_dir: Path,
    height: int,
    header_path: str,
    snapshot_path: str,
    header_hash: str,
    app_hash: str,
) -> None:
    live_state = {
        "schema": NODE_LIVE_STATE_SCHEMA,
        "latest_height": height,
        "latest_header_path": _live_state_path_text_v0(
            data_dir=data_dir,
            path=header_path,
            field="latest_header_path",
        ),
        "latest_snapshot_path": _live_state_path_text_v0(
            data_dir=data_dir,
            path=snapshot_path,
            field="latest_snapshot_path",
        ),
        "latest_header_hash": header_hash,
        "latest_app_hash": app_hash,
    }
    _write_json(_latest_live_state_path(data_dir), live_state)


def append_dex_transaction_v0(
    *,
    data_dir: Path,
    tx: Mapping[str, Any],
    time_ms: int,
    min_lp_position_age_seconds: int = 0,
    lp_duration_risk_policy: Any | None = None,
) -> dict[str, Any]:
    """Append one testnet DEX transaction to a node-local live ledger."""

    with _data_dir_writer_lock_v0(data_dir):
        return _append_dex_transaction_v0_locked(
            data_dir=data_dir,
            tx=tx,
            time_ms=time_ms,
            min_lp_position_age_seconds=min_lp_position_age_seconds,
            lp_duration_risk_policy=lp_duration_risk_policy,
        )


def _append_dex_transaction_v0_locked(
    *,
    data_dir: Path,
    tx: Mapping[str, Any],
    time_ms: int,
    min_lp_position_age_seconds: int,
    lp_duration_risk_policy: Any | None,
) -> dict[str, Any]:
    node_status = load_node_status_v0(data_dir)
    bundle_root = Path(str(node_status["bundle_root"]))
    public_manifest = _read_public_manifest(bundle_root)
    bootstrap_manifest = _load_json_object(bundle_root / "bootstrap" / "manifest.json")
    base = _live_base_paths(bundle_root=bundle_root, data_dir=data_dir, node_status=node_status)
    latest_height = int(base["latest_height"])
    tx_id = str(tx.get("tx_id", "")).strip()
    if tx_id:
        existing_report = _existing_append_report_for_tx_id_v0(
            data_dir=data_dir,
            tx_id=tx_id,
            tx=tx,
            max_height=latest_height,
        )
        if existing_report is not None:
            return existing_report
    height = latest_height + 1
    sequencer_id = str(public_manifest["sequencer_id"])
    chain_id = str(public_manifest["chain_id"])
    pre_state_path = Path(str(base["pre_snapshot_path"]))
    pre_state_obj = _load_json_object(pre_state_path)
    pre_snapshot = _dex_snapshot_from_state_file_obj_v0(pre_state_obj)
    dex_config = _local_testnet_tokenomics_dex_config_v0(node_status)
    tx_obj = _attach_tokenomics_buyback_burn_event_v0(
        tx=tx,
        pre_snapshot=pre_snapshot,
        node_status=node_status,
        chain_id=chain_id,
        height=height,
        tx_index=0,
        data_dir=data_dir,
        min_lp_position_age_seconds=min_lp_position_age_seconds,
        lp_duration_risk_policy=lp_duration_risk_policy,
    )
    body = _body_for_tx_v0(
        chain_id=chain_id,
        height=height,
        time_ms=time_ms,
        sequencer_id=sequencer_id,
        tx=tx_obj,
    )
    live_body_path = data_dir / "live_bodies" / f"{height}.json"
    _write_json(live_body_path, body)
    live_ledger_dir = data_dir / "live_ledger"
    operations = tx_obj.get("operations")
    use_tau_app_state = _is_tau_app_state_obj_v0(pre_state_obj) or (
        isinstance(operations, Mapping) and "10" in operations
    )
    if use_tau_app_state:
        chain_balances_path = data_dir / "live_chain_balances" / f"{height}.json"
        _write_json(chain_balances_path, _native_chain_balances_from_snapshot_v0(pre_snapshot))
        block_report = build_local_block_v0(
            body_path=live_body_path,
            out_dir=live_ledger_dir,
            time_ms=time_ms,
            tau_app_state_path=pre_state_path,
            tau_chain_balances_path=chain_balances_path,
            tau_chain_id=chain_id,
            prev_header_path=Path(str(base["prev_header_path"])),
            trusted_prev_header_hash=ZERO_ROOT,
            sequencer_set_hash=str(bootstrap_manifest["sequencer_set_hash"]),
            data_availability_root=ZERO_ROOT,
            proof_journal_hash=ZERO_ROOT,
            config_digest=str(bootstrap_manifest["config_digest"]),
            module_versions_digest=str(bootstrap_manifest["module_versions_digest"]),
            signature_set_root=ZERO_ROOT,
            allow_missing_settlement=True,
            require_intent_signatures=True,
            allow_unsigned_intents_if_tx_sender_matches=False,
            tau_enable_faucet=isinstance(operations, Mapping) and "7" in operations,
        )
    else:
        block_report = _build_dex_block_with_tokenomics_buyback_v0(
            data_dir=data_dir,
            body_path=live_body_path,
            out_dir=live_ledger_dir,
            time_ms=time_ms,
            pre_snapshot_path=pre_state_path,
            prev_header_path=Path(str(base["prev_header_path"])),
            trusted_prev_header_hash=ZERO_ROOT,
            sequencer_set_hash=str(bootstrap_manifest["sequencer_set_hash"]),
            data_availability_root=ZERO_ROOT,
            proof_journal_hash=ZERO_ROOT,
            config_digest=str(bootstrap_manifest["config_digest"]),
            module_versions_digest=str(bootstrap_manifest["module_versions_digest"]),
            signature_set_root=ZERO_ROOT,
            allow_missing_settlement=True,
            require_intent_signatures=True,
            allow_unsigned_intents_if_tx_sender_matches=False,
            protocol_fee_share_bps=dex_config.protocol_fee_share_bps,
            protocol_fee_recipient_pubkey=dex_config.protocol_fee_recipient_pubkey,
            min_lp_position_age_seconds=min_lp_position_age_seconds,
            lp_duration_risk_policy=lp_duration_risk_policy,
        )
    receipts_path = Path(str(block_report["receipts_path"]))
    receipts = json.loads(receipts_path.read_text(encoding="utf-8"))
    accepted = bool(receipts and isinstance(receipts[0], Mapping) and receipts[0].get("accepted") is True)
    post_state_path = block_report.get("post_snapshot_path", block_report.get("post_app_state_path"))
    if post_state_path is None:
        raise ValueError("block report missing post state path")
    _write_live_state(
        data_dir=data_dir,
        height=height,
        header_path=str(block_report["header_path"]),
        snapshot_path=str(post_state_path),
        header_hash=str(block_report["header_hash"]),
        app_hash=str(block_report["app_hash"]),
    )
    report = {
        "schema": NODE_APPEND_REPORT_SCHEMA,
        "ok": True,
        "status": "accepted",
        "node_id": node_status["node_id"],
        "tx_accepted": accepted,
        "height": height,
        "tx_hash": tx_hash_v0(dict(tx_obj)),
        "header_hash": block_report["header_hash"],
        "app_hash": block_report["app_hash"],
        "body_path": block_report["body_path"],
        "header_path": block_report["header_path"],
        "checkpoint_path": block_report["checkpoint_path"],
        "receipts_path": block_report["receipts_path"],
        "post_snapshot_path": str(post_state_path),
        "receipt": receipts[0] if receipts else None,
    }
    if "post_app_state_path" in block_report:
        report["post_app_state_path"] = block_report["post_app_state_path"]
    append_report_path = data_dir / "append_reports" / f"{height}.json"
    _write_json(append_report_path, report)
    return {**report, "append_report_path": str(append_report_path)}


def _build_faucet_block_from_body_v0(
    *,
    data_dir: Path,
    body: Mapping[str, Any],
    time_ms: int,
    prev_header_path: Path,
    pre_snapshot_path: Path,
    sequencer_set_hash: str,
    config_digest: str,
    module_versions_digest: str,
) -> dict[str, Any]:
    body_obj = dict(body)
    validate_body_v0(body_obj)
    if not _is_faucet_body_v0(body_obj):
        raise ValueError("body is not a testnet faucet body")
    tx = dict(body_obj["transactions"][0])
    to_pubkey = _require_pubkey_v0(tx.get("to_pubkey"), name="faucet.to_pubkey")
    asset = _require_asset_v0(tx.get("asset"), name="faucet.asset")
    amount = _require_positive_amount_v0(
        tx.get("amount"),
        name="faucet.amount",
        maximum=MAX_TESTNET_FAUCET_AMOUNT,
    )
    try:
        protocol_token_asset_id = _protocol_token_asset_id_from_status_v0(load_node_status_v0(data_dir))
    except Exception:
        protocol_token_asset_id = None
    if protocol_token_asset_id is not None and asset == protocol_token_asset_id:
        raise ValueError("protocol_token_faucet_forbidden")
    pre_snapshot_obj = _load_json_object(pre_snapshot_path)
    pre_snapshot = _dex_snapshot_from_state_file_obj_v0(pre_snapshot_obj)
    pre_state = state_from_snapshot(pre_snapshot)
    pre_state_root = _state_root_for_state_file_obj_v0(pre_snapshot_obj)
    pre_state.balances.add(to_pubkey, asset, amount)
    post_dex_snapshot = snapshot_from_state(pre_state).data
    post_snapshot = _replace_dex_snapshot_in_state_file_obj_v0(pre_snapshot_obj, post_dex_snapshot)
    post_state_root = _state_root_for_state_file_obj_v0(post_snapshot)
    height = int(body_obj["height"])
    chain_id = str(body_obj["chain_id"])
    prev_header = dict(_load_json_object(prev_header_path))
    prev_header_hash = canonical_header_hash_v0(prev_header)
    evidence_root = compute_evidence_root_v0(body_obj["evidence"])
    app_hash = compute_app_hash_v0(
        {
            "chain_id": chain_id,
            "height": height,
            "post_state_root": post_state_root,
            "evidence_root": evidence_root,
            "config_digest": config_digest,
            "module_versions_digest": module_versions_digest,
        }
    )
    header = build_header_v0(
        chain_id=chain_id,
        height=height,
        time_ms=time_ms,
        prev_header_hash=prev_header_hash,
        sequencer_set_hash=sequencer_set_hash,
        ingress_root=compute_ingress_root_v0(body_obj["ingress"]),
        tx_root=compute_tx_root_v0(body_obj["transactions"]),
        pre_state_root=pre_state_root,
        post_state_root=post_state_root,
        app_hash=app_hash,
        evidence_root=evidence_root,
        body_root=canonical_body_root_v0(body_obj),
        data_availability_root=ZERO_ROOT,
        proof_journal_hash=ZERO_ROOT,
        config_digest=config_digest,
        module_versions_digest=module_versions_digest,
        signature_set_root=ZERO_ROOT,
    )
    checkpoint = build_checkpoint_v0(header)
    header_hash = canonical_header_hash_v0(header)
    tx_hash = tx_hash_v0(tx)
    receipt = build_tx_receipt_v0(
        tx_hash=tx_hash,
        height=height,
        index=0,
        accepted=True,
        error_code=None,
        state_changed=True,
    )
    live_ledger_dir = data_dir / "live_ledger"
    header_path = live_ledger_dir / "headers" / f"{height}.json"
    body_path = live_ledger_dir / "bodies" / f"{height}.json"
    checkpoint_path = live_ledger_dir / "checkpoints" / f"{height}.json"
    receipts_path = live_ledger_dir / "receipts" / f"{height}.json"
    snapshot_path = live_ledger_dir / "snapshots" / f"{height}.json"
    _write_json(header_path, header)
    _write_json(body_path, body_obj)
    _write_json(checkpoint_path, checkpoint)
    _write_json(receipts_path, [receipt])
    _write_json(snapshot_path, post_snapshot)
    return {
        "height": height,
        "tx_hash": tx_hash,
        "header_hash": header_hash,
        "app_hash": app_hash,
        "body_path": str(body_path),
        "header_path": str(header_path),
        "checkpoint_path": str(checkpoint_path),
        "receipts_path": str(receipts_path),
        "post_snapshot_path": str(snapshot_path),
        "receipt": receipt,
    }


def _build_tokenomics_reward_claim_block_from_body_v0(
    *,
    data_dir: Path,
    body: Mapping[str, Any],
    time_ms: int,
    prev_header_path: Path,
    pre_snapshot_path: Path,
    sequencer_set_hash: str,
    config_digest: str,
    module_versions_digest: str,
) -> dict[str, Any]:
    body_obj = dict(body)
    validate_body_v0(body_obj)
    if not _is_tokenomics_reward_claim_body_v0(body_obj):
        raise ValueError("body is not a tokenomics reward claim body")
    node_status = load_node_status_v0(data_dir)
    distribution = node_status.get("token_distribution")
    if not isinstance(distribution, Mapping) or not distribution:
        raise ValueError("token_distribution_missing")
    distribution_obj = dict(distribution)
    validate_protocol_token_distribution_v0(distribution_obj)
    tx = dict(body_obj["transactions"][0])
    claim_raw = tx.get("claim")
    if not isinstance(claim_raw, Mapping):
        raise ValueError("tokenomics reward claim missing claim")
    claim_height = int(body_obj["height"])
    source = _source_receipt_for_tokenomics_claim_v0(
        data_dir=data_dir,
        source_height=_ui_amount_int_v0(
            claim_raw.get("source_height"),
            name="claim.source_height",
            maximum=9_223_372_036_854_775_807,
        ),
        source_tx_index=_ui_amount_int_v0(
            claim_raw.get("source_tx_index"),
            name="claim.source_tx_index",
            maximum=1_000_000,
            allow_zero=True,
        ),
        recipient_pubkey=str(claim_raw.get("recipient_pubkey", "")),
        requested_receipt_hash=str(claim_raw.get("receipt_hash", "")),
        requested_receipt_kind=str(claim_raw.get("receipt_kind", "")),
        max_source_height=claim_height - 1,
    )
    if source["source_tx_hash"] != claim_raw.get("source_tx_hash"):
        raise ValueError("tokenomics reward claim source_tx_hash mismatch")
    program = active_participant_program_by_id_v0(distribution_obj, str(claim_raw.get("program_id", "")))
    token_asset_id = str(distribution_obj["token_asset_id"])
    pre_snapshot_obj = _load_json_object(pre_snapshot_path)
    pre_snapshot = _dex_snapshot_from_state_file_obj_v0(pre_snapshot_obj)
    pre_state = state_from_snapshot(pre_snapshot)
    source_balance = pre_state.balances.get(str(program["controller_pubkey"]), token_asset_id)
    spent_by_program, claimed_keys = _tokenomics_claim_index_from_live_bodies_v0(
        data_dir=data_dir,
        max_height=claim_height - 1,
    )
    claim = validate_active_participant_reward_claim_v0(
        claim_raw,
        distribution=distribution_obj,
        spent_by_program=spent_by_program,
        claimed_keys=claimed_keys,
        reward_source_balance=source_balance,
    )
    pre_state_root = _state_root_for_state_file_obj_v0(pre_snapshot_obj)
    pre_state.balances.subtract(str(claim["controller_pubkey"]), token_asset_id, int(claim["amount"]))
    pre_state.balances.add(str(claim["recipient_pubkey"]), token_asset_id, int(claim["amount"]))
    post_dex_snapshot = snapshot_from_state(pre_state).data
    post_snapshot = _replace_dex_snapshot_in_state_file_obj_v0(pre_snapshot_obj, post_dex_snapshot)
    post_state_root = _state_root_for_state_file_obj_v0(post_snapshot)
    chain_id = str(body_obj["chain_id"])
    prev_header = dict(_load_json_object(prev_header_path))
    prev_header_hash = canonical_header_hash_v0(prev_header)
    evidence_root = compute_evidence_root_v0(body_obj["evidence"])
    app_hash = compute_app_hash_v0(
        {
            "chain_id": chain_id,
            "height": claim_height,
            "post_state_root": post_state_root,
            "evidence_root": evidence_root,
            "config_digest": config_digest,
            "module_versions_digest": module_versions_digest,
        }
    )
    header = build_header_v0(
        chain_id=chain_id,
        height=claim_height,
        time_ms=time_ms,
        prev_header_hash=prev_header_hash,
        sequencer_set_hash=sequencer_set_hash,
        ingress_root=compute_ingress_root_v0(body_obj["ingress"]),
        tx_root=compute_tx_root_v0(body_obj["transactions"]),
        pre_state_root=pre_state_root,
        post_state_root=post_state_root,
        app_hash=app_hash,
        evidence_root=evidence_root,
        body_root=canonical_body_root_v0(body_obj),
        data_availability_root=ZERO_ROOT,
        proof_journal_hash=ZERO_ROOT,
        config_digest=config_digest,
        module_versions_digest=module_versions_digest,
        signature_set_root=ZERO_ROOT,
    )
    checkpoint = build_checkpoint_v0(header)
    header_hash = canonical_header_hash_v0(header)
    tx_hash = tx_hash_v0(tx)
    receipt = build_tx_receipt_v0(
        tx_hash=tx_hash,
        height=claim_height,
        index=0,
        accepted=True,
        error_code=None,
        state_changed=True,
    )
    live_ledger_dir = data_dir / "live_ledger"
    header_path = live_ledger_dir / "headers" / f"{claim_height}.json"
    body_path = live_ledger_dir / "bodies" / f"{claim_height}.json"
    checkpoint_path = live_ledger_dir / "checkpoints" / f"{claim_height}.json"
    receipts_path = live_ledger_dir / "receipts" / f"{claim_height}.json"
    snapshot_path = live_ledger_dir / "snapshots" / f"{claim_height}.json"
    _write_json(header_path, header)
    _write_json(body_path, body_obj)
    _write_json(checkpoint_path, checkpoint)
    _write_json(receipts_path, [receipt])
    _write_json(snapshot_path, post_snapshot)
    return {
        "height": claim_height,
        "tx_hash": tx_hash,
        "header_hash": header_hash,
        "app_hash": app_hash,
        "body_path": str(body_path),
        "header_path": str(header_path),
        "checkpoint_path": str(checkpoint_path),
        "receipts_path": str(receipts_path),
        "post_snapshot_path": str(snapshot_path),
        "receipt": receipt,
        "claim": claim,
    }


def _build_dex_block_with_tokenomics_buyback_v0(
    *,
    data_dir: Path,
    body_path: Path,
    out_dir: Path,
    time_ms: int,
    pre_snapshot_path: Path,
    prev_header_path: Path | None,
    trusted_prev_header_hash: str,
    sequencer_set_hash: str,
    data_availability_root: str,
    proof_journal_hash: str,
    config_digest: str,
    module_versions_digest: str,
    signature_set_root: str,
    allow_missing_settlement: bool,
    require_intent_signatures: bool,
    allow_unsigned_intents_if_tx_sender_matches: bool,
    protocol_fee_share_bps: int,
    protocol_fee_recipient_pubkey: str | None,
    min_lp_position_age_seconds: int,
    lp_duration_risk_policy: Any | None,
) -> dict[str, Any]:
    block_report = build_local_block_v0(
        body_path=body_path,
        out_dir=out_dir,
        time_ms=time_ms,
        pre_snapshot_path=pre_snapshot_path,
        prev_header_path=prev_header_path,
        trusted_prev_header_hash=trusted_prev_header_hash,
        sequencer_set_hash=sequencer_set_hash,
        data_availability_root=data_availability_root,
        proof_journal_hash=proof_journal_hash,
        config_digest=config_digest,
        module_versions_digest=module_versions_digest,
        signature_set_root=signature_set_root,
        allow_missing_settlement=allow_missing_settlement,
        require_intent_signatures=require_intent_signatures,
        allow_unsigned_intents_if_tx_sender_matches=allow_unsigned_intents_if_tx_sender_matches,
        protocol_fee_share_bps=protocol_fee_share_bps,
        protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
        min_lp_position_age_seconds=min_lp_position_age_seconds,
        lp_duration_risk_policy=lp_duration_risk_policy,
    )
    return _apply_tokenomics_buyback_burn_to_block_report_v0(
        data_dir=data_dir,
        block_report=block_report,
        pre_snapshot_path=pre_snapshot_path,
        time_ms=time_ms,
        sequencer_set_hash=sequencer_set_hash,
        data_availability_root=data_availability_root,
        proof_journal_hash=proof_journal_hash,
        config_digest=config_digest,
        module_versions_digest=module_versions_digest,
        signature_set_root=signature_set_root,
        protocol_fee_share_bps=protocol_fee_share_bps,
        protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
        min_lp_position_age_seconds=min_lp_position_age_seconds,
        lp_duration_risk_policy=lp_duration_risk_policy,
    )


def _apply_tokenomics_buyback_burn_to_block_report_v0(
    *,
    data_dir: Path,
    block_report: Mapping[str, Any],
    pre_snapshot_path: Path,
    time_ms: int,
    sequencer_set_hash: str,
    data_availability_root: str,
    proof_journal_hash: str,
    config_digest: str,
    module_versions_digest: str,
    signature_set_root: str,
    protocol_fee_share_bps: int,
    protocol_fee_recipient_pubkey: str | None,
    min_lp_position_age_seconds: int,
    lp_duration_risk_policy: Any | None,
) -> dict[str, Any]:
    body_path = Path(str(block_report["body_path"]))
    header_path = Path(str(block_report["header_path"]))
    checkpoint_path = Path(str(block_report["checkpoint_path"]))
    receipts_path = Path(str(block_report["receipts_path"]))
    snapshot_path = Path(str(block_report["post_snapshot_path"]))
    body = dict(_load_json_object(body_path))
    txs = body.get("transactions")
    if not isinstance(txs, list):
        raise ValueError("body transactions must be a list")
    pre_snapshot = _load_json_object(pre_snapshot_path)
    buyback_events: list[dict[str, Any]] = []
    for index, tx in enumerate(txs):
        if not isinstance(tx, Mapping):
            continue
        event = _tokenomics_buyback_event_from_tx_v0(tx)
        if event is not None:
            buyback_events.append({"tx_index": index, "event": dict(event)})
    if not buyback_events:
        return dict(block_report)
    receipts = json.loads(receipts_path.read_text(encoding="utf-8"))
    if not isinstance(receipts, list):
        raise ValueError("receipts must be a list")
    if any(not isinstance(row, Mapping) or row.get("accepted") is not True for row in receipts):
        raise ValueError("tokenomics buyback burn sidecar requires accepted DEX transaction")
    node_status = load_node_status_v0(data_dir)
    distribution = node_status.get("token_distribution")
    if not isinstance(distribution, Mapping) or not distribution:
        raise ValueError("token_distribution_missing")
    distribution_obj = dict(distribution)
    validate_protocol_token_distribution_v0(distribution_obj)
    dex_config = DexConfig(
        protocol_fee_share_bps=protocol_fee_share_bps,
        protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
    )
    token_asset_id = str(distribution_obj["token_asset_id"])
    post_snapshot_obj = _load_json_object(snapshot_path)
    post_state = state_from_snapshot(_dex_snapshot_from_state_file_obj_v0(post_snapshot_obj))
    for wrapped_event in buyback_events:
        tx_index = int(wrapped_event["tx_index"])
        tx = txs[tx_index]
        if not isinstance(tx, Mapping):
            raise ValueError("tokenomics buyback burn transaction malformed")
        event = dict(wrapped_event["event"])
        core_tx = json.loads(json.dumps(tx))
        operations = core_tx.get("operations")
        if isinstance(operations, dict):
            operations.pop(TOKENOMICS_BUYBACK_BURN_OP_STREAM, None)
        result = _compute_dex_result_for_tokenomics_tx_v0(
            pre_snapshot=pre_snapshot,
            tx=core_tx,
            chain_id=str(body["chain_id"]),
            dex_config=dex_config,
            min_lp_position_age_seconds=min_lp_position_age_seconds,
            lp_duration_risk_policy=lp_duration_risk_policy,
        )
        if result is None or result.settlement is None or result.state is None:
            raise ValueError("tokenomics buyback burn sidecar without accepted fee-bearing DEX settlement")
        total_fee = sum(int(fill.fee_paid or 0) for fill in result.settlement.fills)
        if total_fee <= 0:
            raise ValueError("tokenomics buyback burn sidecar without accepted fee-bearing DEX settlement")
        result_snapshot = snapshot_from_state(result.state).data
        pre_supply, pre_balances_by_pubkey = _token_balance_sum_from_snapshot_v0(result_snapshot, asset_id=token_asset_id)
        source_pubkey_expected = _tokenomics_buyback_source_pubkey_v0(distribution_obj)
        buyback_index = _tokenomics_buyback_index_from_live_bodies_v0(data_dir=data_dir, max_height=int(body["height"]) - 1)
        expected_market_purchase = _market_buyback_purchase_from_state_v0(
            state=result.state,
            source_pubkey=source_pubkey_expected,
            token_asset_id=token_asset_id,
            protocol_fee_by_asset=_protocol_fee_by_asset_from_result_v0(result, core_tx),
            current_supply_before=pre_supply,
            supply_floor=int(distribution_obj["supply_floor"]),
        )
        expected_execution_mode = (
            "market_purchase_then_burn"
            if expected_market_purchase is not None
            else "treasury_allocation_burn_only"
        )
        expected_event = build_tokenomics_buyback_burn_event_v0(
            distribution=distribution_obj,
            chain_id=str(body["chain_id"]),
            height=int(body["height"]),
            tx_index=tx_index,
            tx_hash=tx_hash_v0(core_tx),
            total_swap_fee=total_fee,
            carry_before=int(buyback_index["buyback_carry_after"]),
            source_balance_before=int(pre_balances_by_pubkey.get(source_pubkey_expected, 0)),
            current_supply_before=pre_supply,
            buyback_share_bps=LOCAL_TESTNET_BUYBACK_SHARE_BPS,
            source_allocation_id=LOCAL_TESTNET_BUYBACK_SOURCE_ALLOCATION_ID,
            execution_mode=expected_execution_mode,
            market_purchase=expected_market_purchase,
            production_security_claim=False,
        )
        if event != expected_event:
            raise ValueError("tokenomics buyback burn event does not match deterministic replay")
        validated = validate_tokenomics_buyback_burn_event_v0(event, distribution=distribution_obj)
        source_pubkey = str(validated["source_pubkey"])
        burn_amount = int(validated["burn_amount"])
        if validated.get("execution_mode") == "market_purchase_then_burn":
            market_purchase = validated.get("market_purchase")
            if not isinstance(market_purchase, Mapping):
                raise ValueError("tokenomics buyback market purchase missing")
            pool_id = str(market_purchase["pool_id"])
            quote_asset = str(market_purchase["quote_asset_id"])
            quote_amount_in = int(market_purchase["quote_amount_in"])
            pool = post_state.pools.get(pool_id)
            if pool is None:
                raise ValueError("tokenomics buyback market pool missing")
            post_state.balances.subtract(source_pubkey, quote_asset, quote_amount_in)
            pool.reserve0 = int(market_purchase["reserve0_after"])
            pool.reserve1 = int(market_purchase["reserve1_after"])
        elif burn_amount > 0:
            post_state.balances.subtract(source_pubkey, token_asset_id, burn_amount)
    updated_dex_snapshot = snapshot_from_state(post_state).data
    updated_snapshot = _replace_dex_snapshot_in_state_file_obj_v0(post_snapshot_obj, updated_dex_snapshot)
    post_state_root = _state_root_for_state_file_obj_v0(updated_snapshot)
    header_old = dict(_load_json_object(header_path))
    chain_id = str(body["chain_id"])
    height = int(body["height"])
    evidence_root = compute_evidence_root_v0(body["evidence"])
    app_hash = compute_app_hash_v0(
        {
            "chain_id": chain_id,
            "height": height,
            "post_state_root": post_state_root,
            "evidence_root": evidence_root,
            "config_digest": config_digest,
            "module_versions_digest": module_versions_digest,
        }
    )
    header = build_header_v0(
        chain_id=chain_id,
        height=height,
        time_ms=time_ms,
        prev_header_hash=str(header_old["prev_header_hash"]),
        sequencer_set_hash=sequencer_set_hash,
        ingress_root=compute_ingress_root_v0(body["ingress"]),
        tx_root=compute_tx_root_v0(body["transactions"]),
        pre_state_root=str(header_old["pre_state_root"]),
        post_state_root=post_state_root,
        app_hash=app_hash,
        evidence_root=evidence_root,
        body_root=canonical_body_root_v0(body),
        data_availability_root=data_availability_root,
        proof_journal_hash=proof_journal_hash,
        config_digest=config_digest,
        module_versions_digest=module_versions_digest,
        signature_set_root=signature_set_root,
    )
    checkpoint = build_checkpoint_v0(header)
    header_hash = canonical_header_hash_v0(header)
    _write_json(snapshot_path, updated_snapshot)
    _write_json(header_path, header)
    _write_json(checkpoint_path, checkpoint)
    return {
        **dict(block_report),
        "header_hash": header_hash,
        "app_hash": app_hash,
        "tokenomics_buyback_burn_events": buyback_events,
    }


def append_testnet_faucet_v0(
    *,
    data_dir: Path,
    to_pubkey: str,
    asset: str,
    amount: int,
    time_ms: int,
    tx_id: str = "node-testnet-faucet-v0",
) -> dict[str, Any]:
    """Append a testnet-only faucet mint to the node-local live ledger."""

    with _data_dir_writer_lock_v0(data_dir):
        return _append_testnet_faucet_v0_locked(
            data_dir=data_dir,
            to_pubkey=to_pubkey,
            asset=asset,
            amount=amount,
            time_ms=time_ms,
            tx_id=tx_id,
        )


def _append_testnet_faucet_v0_locked(
    *,
    data_dir: Path,
    to_pubkey: str,
    asset: str,
    amount: int,
    time_ms: int,
    tx_id: str,
) -> dict[str, Any]:
    node_status = load_node_status_v0(data_dir)
    bundle_root = Path(str(node_status["bundle_root"]))
    public_manifest = _read_public_manifest(bundle_root)
    bootstrap_manifest = _load_json_object(bundle_root / "bootstrap" / "manifest.json")
    base = _live_base_paths(bundle_root=bundle_root, data_dir=data_dir, node_status=node_status)
    latest_height = int(base["latest_height"])
    height = latest_height + 1
    tx = _faucet_tx_v0(
        tx_id=tx_id,
        to_pubkey=_require_pubkey_v0(to_pubkey, name="to_pubkey"),
        asset=_require_asset_v0(asset, name="asset"),
        amount=_require_positive_amount_v0(amount, name="amount", maximum=MAX_TESTNET_FAUCET_AMOUNT),
    )
    protocol_token_asset_id = _protocol_token_asset_id_from_status_v0(node_status)
    if protocol_token_asset_id is not None and tx["asset"] == protocol_token_asset_id:
        raise ValueError("protocol_token_faucet_forbidden")
    existing_report = _existing_append_report_for_tx_id_v0(
        data_dir=data_dir,
        tx_id=tx_id,
        tx=tx,
        max_height=latest_height,
    )
    if existing_report is not None:
        return existing_report
    body = _body_for_tx_v0(
        chain_id=str(public_manifest["chain_id"]),
        height=height,
        time_ms=time_ms,
        sequencer_id=str(public_manifest["sequencer_id"]),
        tx=tx,
    )
    block_report = _build_faucet_block_from_body_v0(
        data_dir=data_dir,
        body=body,
        time_ms=time_ms,
        prev_header_path=Path(str(base["prev_header_path"])),
        pre_snapshot_path=Path(str(base["pre_snapshot_path"])),
        sequencer_set_hash=str(bootstrap_manifest["sequencer_set_hash"]),
        config_digest=str(bootstrap_manifest["config_digest"]),
        module_versions_digest=str(bootstrap_manifest["module_versions_digest"]),
    )
    _write_live_state(
        data_dir=data_dir,
        height=height,
        header_path=str(block_report["header_path"]),
        snapshot_path=str(block_report["post_snapshot_path"]),
        header_hash=str(block_report["header_hash"]),
        app_hash=str(block_report["app_hash"]),
    )
    report = {
        "schema": NODE_APPEND_REPORT_SCHEMA,
        "ok": True,
        "status": "accepted",
        "node_id": node_status["node_id"],
        "append_kind": "testnet_faucet",
        **block_report,
    }
    append_report_path = data_dir / "append_reports" / f"{height}.json"
    _write_json(append_report_path, report)
    return {**report, "append_report_path": str(append_report_path)}


def append_tokenomics_reward_claim_v0(
    *,
    data_dir: Path,
    payload: Mapping[str, Any],
    time_ms: int,
) -> dict[str, Any]:
    """Append one local-testnet active-participant reward claim transfer."""

    with _data_dir_writer_lock_v0(data_dir):
        return _append_tokenomics_reward_claim_v0_locked(
            data_dir=data_dir,
            payload=payload,
            time_ms=time_ms,
        )


def _append_tokenomics_reward_claim_v0_locked(
    *,
    data_dir: Path,
    payload: Mapping[str, Any],
    time_ms: int,
) -> dict[str, Any]:
    node_status = load_node_status_v0(data_dir)
    bundle_root = Path(str(node_status["bundle_root"]))
    public_manifest = _read_public_manifest(bundle_root)
    bootstrap_manifest = _load_json_object(bundle_root / "bootstrap" / "manifest.json")
    base = _live_base_paths(bundle_root=bundle_root, data_dir=data_dir, node_status=node_status)
    latest_height = int(base["latest_height"])
    height = latest_height + 1
    tx_id_raw = payload.get("tx_id", payload.get("txId"))
    if isinstance(tx_id_raw, str) and tx_id_raw.strip():
        existing = _existing_tx_and_append_report_for_tx_id_v0(
            data_dir=data_dir,
            tx_id=tx_id_raw.strip(),
            max_height=latest_height,
        )
        if existing is not None:
            existing_tx, existing_report = existing
            _validate_tokenomics_claim_idempotent_payload_v0(payload=payload, existing_tx=existing_tx)
            return existing_report
    tx = _ui_tokenomics_reward_claim_tx_v0(
        data_dir=data_dir,
        node_status=node_status,
        payload=payload,
        time_ms=time_ms,
    )
    body = _body_for_tx_v0(
        chain_id=str(public_manifest["chain_id"]),
        height=height,
        time_ms=time_ms,
        sequencer_id=str(public_manifest["sequencer_id"]),
        tx=tx,
    )
    block_report = _build_tokenomics_reward_claim_block_from_body_v0(
        data_dir=data_dir,
        body=body,
        time_ms=time_ms,
        prev_header_path=Path(str(base["prev_header_path"])),
        pre_snapshot_path=Path(str(base["pre_snapshot_path"])),
        sequencer_set_hash=str(bootstrap_manifest["sequencer_set_hash"]),
        config_digest=str(bootstrap_manifest["config_digest"]),
        module_versions_digest=str(bootstrap_manifest["module_versions_digest"]),
    )
    _write_live_state(
        data_dir=data_dir,
        height=height,
        header_path=str(block_report["header_path"]),
        snapshot_path=str(block_report["post_snapshot_path"]),
        header_hash=str(block_report["header_hash"]),
        app_hash=str(block_report["app_hash"]),
    )
    report = {
        "schema": NODE_APPEND_REPORT_SCHEMA,
        "ok": True,
        "status": "accepted",
        "node_id": node_status["node_id"],
        "append_kind": "tokenomics_active_participant_reward_claim",
        **block_report,
        "production_security_claim": False,
    }
    append_report_path = data_dir / "append_reports" / f"{height}.json"
    _write_json(append_report_path, report)
    return {**report, "append_report_path": str(append_report_path)}


def _live_artifact_path(*, data_dir: Path, kind: str, height: int) -> Path:
    if kind == "header":
        return data_dir / "live_ledger" / "headers" / f"{height}.json"
    if kind == "body":
        return data_dir / "live_ledger" / "bodies" / f"{height}.json"
    if kind == "checkpoint":
        return data_dir / "live_ledger" / "checkpoints" / f"{height}.json"
    if kind == "snapshot":
        return data_dir / "live_ledger" / "snapshots" / f"{height}.json"
    raise ValueError(f"unsupported live artifact kind: {kind}")


def _discard_replayed_block_artifacts_v0(*, data_dir: Path, block_report: Mapping[str, Any]) -> None:
    data_root = data_dir.resolve()
    for key in ("header_path", "body_path", "checkpoint_path", "receipts_path", "post_snapshot_path"):
        value = block_report.get(key)
        if not isinstance(value, str) or value == "":
            continue
        try:
            path = Path(value).resolve()
        except OSError:
            continue
        if path == data_root or data_root not in path.parents:
            continue
        try:
            path.unlink(missing_ok=True)
        except OSError:
            continue


def pull_live_from_peer_v0(
    *,
    data_dir: Path,
    peer_url: str,
    min_lp_position_age_seconds: int = 0,
    lp_duration_risk_policy: Any | None = None,
) -> dict[str, Any]:
    """Pull live blocks from a peer and accept only deterministic replays."""

    with _data_dir_writer_lock_v0(data_dir):
        return _pull_live_from_peer_v0_locked(
            data_dir=data_dir,
            peer_url=peer_url,
            min_lp_position_age_seconds=min_lp_position_age_seconds,
            lp_duration_risk_policy=lp_duration_risk_policy,
        )


def _pull_live_from_peer_v0_locked(
    *,
    data_dir: Path,
    peer_url: str,
    min_lp_position_age_seconds: int,
    lp_duration_risk_policy: Any | None,
) -> dict[str, Any]:
    peer_admission = check_peer_status_v0(data_dir=data_dir, peer_urls=[peer_url])
    if peer_admission.get("ok") is not True:
        # Surface enough detail for the follower poll loop to distinguish a
        # fork ("common_header_match" false) from a down peer ("error"
        # populated) without an operator having to scrape logs.
        peer_report: Mapping[str, Any] = {}
        reports = peer_admission.get("peers")
        if isinstance(reports, list) and reports and isinstance(reports[0], Mapping):
            peer_report = reports[0]
        diag = {
            "common_header_match": peer_report.get("common_header_match"),
            "common_height": peer_report.get("common_height"),
            "local_common_header_hash": peer_report.get("local_common_header_hash"),
            "peer_common_header_hash": peer_report.get("peer_common_header_hash"),
            "height_relation": peer_report.get("height_relation"),
            "peer_error": peer_report.get("error"),
        }
        raise ValueError(f"peer admission rejected: {json.dumps(diag, sort_keys=True)}")

    node_status = load_node_status_v0(data_dir)
    bundle_root = Path(str(node_status["bundle_root"]))
    public_manifest = _read_public_manifest(bundle_root)
    bootstrap_manifest = _load_json_object(bundle_root / "bootstrap" / "manifest.json")
    base = _live_base_paths(bundle_root=bundle_root, data_dir=data_dir, node_status=node_status)
    local_latest = int(base["latest_height"])
    peer_live = _fetch_json_url(urljoin(peer_url.rstrip("/") + "/", "live"))
    if peer_live.get("ok") is not True or peer_live.get("live") is not True:
        return {
            "schema": NODE_PULL_REPORT_SCHEMA,
            "ok": True,
            "status": "accepted",
            "pulled_count": 0,
            "local_latest_height": local_latest,
            "peer_live": False,
            "peer_admission": peer_admission,
        }
    peer_state = peer_live.get("state")
    if not isinstance(peer_state, Mapping):
        raise ValueError("peer live state must be an object")
    peer_latest = int(peer_state["latest_height"])
    if peer_latest <= local_latest:
        # Divergent-head detection at the common height is handled by
        # check_peer_status_v0 above (admission rejected if peer's header at
        # min(local, peer) disagrees). When admission passes and peer is
        # behind, follower is the better chain — no pull needed.
        return {
            "schema": NODE_PULL_REPORT_SCHEMA,
            "ok": True,
            "status": "accepted",
            "pulled_count": 0,
            "local_latest_height": local_latest,
            "peer_latest_height": peer_latest,
            "peer_admission": peer_admission,
        }

    pulled: list[dict[str, Any]] = []
    current_prev_header = Path(str(base["prev_header_path"]))
    current_pre_snapshot = Path(str(base["pre_snapshot_path"]))
    live_ledger_dir = data_dir / "live_ledger"
    for height in range(local_latest + 1, peer_latest + 1):
        peer_body = _fetch_json_url(urljoin(peer_url.rstrip("/") + "/", f"live/body/{height}"))
        peer_header = _fetch_json_url(urljoin(peer_url.rstrip("/") + "/", f"live/header/{height}"))
        if _is_faucet_body_v0(peer_body):
            block_report = _build_faucet_block_from_body_v0(
                data_dir=data_dir,
                body=peer_body,
                time_ms=int(peer_header["time_ms"]),
                prev_header_path=current_prev_header,
                pre_snapshot_path=current_pre_snapshot,
                sequencer_set_hash=str(bootstrap_manifest["sequencer_set_hash"]),
                config_digest=str(bootstrap_manifest["config_digest"]),
                module_versions_digest=str(bootstrap_manifest["module_versions_digest"]),
            )
        elif _is_tokenomics_reward_claim_body_v0(peer_body):
            block_report = _build_tokenomics_reward_claim_block_from_body_v0(
                data_dir=data_dir,
                body=peer_body,
                time_ms=int(peer_header["time_ms"]),
                prev_header_path=current_prev_header,
                pre_snapshot_path=current_pre_snapshot,
                sequencer_set_hash=str(bootstrap_manifest["sequencer_set_hash"]),
                config_digest=str(bootstrap_manifest["config_digest"]),
                module_versions_digest=str(bootstrap_manifest["module_versions_digest"]),
            )
        else:
            body_path = data_dir / "pulled_bodies" / f"{height}.json"
            _write_json(body_path, peer_body)
            dex_config = _local_testnet_tokenomics_dex_config_v0(load_node_status_v0(data_dir))
            block_report = _build_dex_block_with_tokenomics_buyback_v0(
                data_dir=data_dir,
                body_path=body_path,
                out_dir=live_ledger_dir,
                time_ms=int(peer_header["time_ms"]),
                pre_snapshot_path=current_pre_snapshot,
                prev_header_path=current_prev_header,
                trusted_prev_header_hash=ZERO_ROOT,
                sequencer_set_hash=str(bootstrap_manifest["sequencer_set_hash"]),
                data_availability_root=ZERO_ROOT,
                proof_journal_hash=ZERO_ROOT,
                config_digest=str(bootstrap_manifest["config_digest"]),
                module_versions_digest=str(bootstrap_manifest["module_versions_digest"]),
                signature_set_root=ZERO_ROOT,
                allow_missing_settlement=True,
                require_intent_signatures=True,
                allow_unsigned_intents_if_tx_sender_matches=False,
                protocol_fee_share_bps=dex_config.protocol_fee_share_bps,
                protocol_fee_recipient_pubkey=dex_config.protocol_fee_recipient_pubkey,
                min_lp_position_age_seconds=min_lp_position_age_seconds,
                lp_duration_risk_policy=lp_duration_risk_policy,
            )
        local_header = _load_json_object(Path(str(block_report["header_path"])))
        if dict(local_header) != dict(peer_header):
            _discard_replayed_block_artifacts_v0(data_dir=data_dir, block_report=block_report)
            raise ValueError(f"peer header mismatch at height {height}")
        if canonical_header_hash_v0(dict(local_header)) != canonical_header_hash_v0(dict(peer_header)):
            _discard_replayed_block_artifacts_v0(data_dir=data_dir, block_report=block_report)
            raise ValueError(f"peer header hash mismatch at height {height}")
        current_prev_header = Path(str(block_report["header_path"]))
        current_pre_snapshot = Path(str(block_report["post_snapshot_path"]))
        _write_live_state(
            data_dir=data_dir,
            height=height,
            header_path=str(current_prev_header),
            snapshot_path=str(current_pre_snapshot),
            header_hash=str(block_report["header_hash"]),
            app_hash=str(block_report["app_hash"]),
        )
        pulled.append(
            {
                "height": height,
                "header_hash": block_report["header_hash"],
                "app_hash": block_report["app_hash"],
            }
        )

    report = {
        "schema": NODE_PULL_REPORT_SCHEMA,
        "ok": True,
        "status": "accepted",
        "peer_url": peer_url,
        "network_id": public_manifest["network_id"],
        "chain_id": public_manifest["chain_id"],
        "from_height": local_latest + 1,
        "to_height": peer_latest,
        "pulled_count": len(pulled),
        "pulled": pulled,
        "local_latest_height": peer_latest,
        "peer_admission": peer_admission,
    }
    pull_report_path = data_dir / "pull_reports" / f"{peer_latest}.json"
    _write_json(pull_report_path, report)
    return {**report, "pull_report_path": str(pull_report_path)}


def load_node_status_v0(data_dir: Path) -> dict[str, Any]:
    status = dict(_load_json_object(data_dir / "node_status.json"))
    if status.get("schema") != NODE_STATUS_SCHEMA:
        raise ValueError("node status schema mismatch")
    if status.get("node_status_hash") != _node_status_hash(status):
        raise ValueError("node status hash mismatch")
    return status


def _local_header_hash_at_height_v0(*, data_dir: Path, bundle_root: Path, height: int) -> str:
    live_header_path = _live_artifact_path(data_dir=data_dir, kind="header", height=height)
    if live_header_path.is_file():
        return canonical_header_hash_v0(dict(_load_json_object(live_header_path)))
    bootstrap_header_path = bundle_root / "bootstrap" / "ledger" / "headers" / f"{height}.json"
    if bootstrap_header_path.is_file():
        return canonical_header_hash_v0(dict(_load_json_object(bootstrap_header_path)))
    raise ValueError(f"local header missing at height {height}")


def _local_tip_v0(*, data_dir: Path, node_status: Mapping[str, Any]) -> dict[str, Any]:
    live_path = _latest_live_state_path(data_dir)
    if live_path.is_file():
        live_state = dict(_load_live_state_v0(data_dir, node_status=node_status))
        return {
            "live": True,
            "height": int(live_state["latest_height"]),
            "header_hash": str(live_state["latest_header_hash"]),
            "app_hash": str(live_state["latest_app_hash"]),
        }
    return {
        "live": False,
        "height": int(node_status["latest_height"]),
        "header_hash": str(node_status["last_header_hash"]),
        "app_hash": str(node_status["last_app_hash"]),
    }


def _peer_tip_from_http_v0(*, peer_url: str, peer_status: Mapping[str, Any]) -> dict[str, Any]:
    peer_live = _fetch_json_url(urljoin(peer_url.rstrip("/") + "/", "live"))
    if peer_live.get("ok") is True and peer_live.get("live") is True:
        state = peer_live.get("state")
        if not isinstance(state, Mapping):
            raise ValueError("peer live state must be an object")
        return {
            "live": True,
            "height": int(state["latest_height"]),
            "header_hash": str(state["latest_header_hash"]),
            "app_hash": str(state["latest_app_hash"]),
        }
    return {
        "live": False,
        "height": int(peer_status["latest_height"]),
        "header_hash": str(peer_status["last_header_hash"]),
        "app_hash": str(peer_status["last_app_hash"]),
    }


def _peer_header_hash_at_height_v0(
    *,
    peer_url: str,
    peer_status: Mapping[str, Any],
    height: int,
) -> str:
    bootstrap_latest = int(peer_status["latest_height"])
    if height == bootstrap_latest:
        return str(peer_status["last_header_hash"])
    if height > bootstrap_latest:
        peer_header = _fetch_json_url(urljoin(peer_url.rstrip("/") + "/", f"live/header/{height}"))
        return canonical_header_hash_v0(dict(peer_header))
    raise ValueError(f"cannot fetch peer bootstrap header at height {height}")


def check_peer_status_v0(*, data_dir: Path, peer_urls: list[str]) -> dict[str, Any]:
    """Check that peer nodes are on the same network and common live prefix."""

    node_status = load_node_status_v0(data_dir)
    bundle_root = Path(str(node_status["bundle_root"]))
    local_tip = _local_tip_v0(data_dir=data_dir, node_status=node_status)
    peer_reports: list[dict[str, Any]] = []
    for peer_url in peer_urls:
        try:
            peer_status = _fetch_json_url(urljoin(peer_url.rstrip("/") + "/", "status"))
            if peer_status.get("schema") != NODE_STATUS_SCHEMA:
                raise ValueError("peer node status schema mismatch")
            if peer_status.get("node_status_hash") != _node_status_hash(peer_status):
                raise ValueError("peer node status hash mismatch")
            peer_tip = _peer_tip_from_http_v0(peer_url=peer_url, peer_status=peer_status)
            network_match = peer_status.get("network_id") == node_status.get("network_id")
            chain_match = peer_status.get("chain_id") == node_status.get("chain_id")
            feature_suite_match = peer_status.get("feature_suite_hash") == node_status.get("feature_suite_hash")
            common_height = min(int(local_tip["height"]), int(peer_tip["height"]))
            if common_height == int(local_tip["height"]):
                local_common_hash = str(local_tip["header_hash"])
            else:
                local_common_hash = _local_header_hash_at_height_v0(
                    data_dir=data_dir,
                    bundle_root=bundle_root,
                    height=common_height,
                )
            peer_common_hash = _peer_header_hash_at_height_v0(
                peer_url=peer_url,
                peer_status=peer_status,
                height=common_height,
            )
            common_header_match = local_common_hash == peer_common_hash
            compatible = bool(network_match and chain_match and feature_suite_match and common_header_match)
            if int(peer_tip["height"]) > int(local_tip["height"]):
                relation = "peer_ahead"
            elif int(peer_tip["height"]) < int(local_tip["height"]):
                relation = "peer_behind"
            else:
                relation = "same_height"
            peer_reports.append(
                {
                    "peer_url": peer_url,
                    "ok": compatible,
                    "status": "accepted" if compatible else "rejected",
                    "peer_node_id": peer_status.get("node_id"),
                    "network_match": network_match,
                    "chain_match": chain_match,
                    "feature_suite_match": feature_suite_match,
                    "common_header_match": common_header_match,
                    "height_relation": relation,
                    "local_tip": local_tip,
                    "peer_tip": peer_tip,
                    "common_height": common_height,
                    "common_header_hash": local_common_hash if common_header_match else None,
                    "local_common_header_hash": local_common_hash,
                    "peer_common_header_hash": peer_common_hash,
                }
            )
        except Exception as exc:
            peer_reports.append(
                {
                    "peer_url": peer_url,
                    "ok": False,
                    "status": "rejected",
                    "error": str(exc),
                    "local_tip": local_tip,
                }
            )
    ok = all(report.get("ok") is True for report in peer_reports)
    return {
        "schema": NODE_PEER_CHECK_REPORT_SCHEMA,
        "ok": ok,
        "status": "accepted" if ok else "rejected",
        "node_id": node_status["node_id"],
        "network_id": node_status["network_id"],
        "chain_id": node_status["chain_id"],
        "feature_suite_hash": node_status["feature_suite_hash"],
        "local_tip": local_tip,
        "peer_count": len(peer_reports),
        "peers": peer_reports,
    }


def _load_optional_json(path_text: object) -> object | None:
    if not isinstance(path_text, str) or path_text == "":
        return None
    path = Path(path_text)
    if not path.is_file():
        return None
    return _load_json_object(path)


def _public_base_url_from_headers_v0(headers: Mapping[str, str]) -> str:
    host = str(headers.get("X-Forwarded-Host") or headers.get("Host") or "").strip()
    if not host:
        host = "127.0.0.1"
    raw_proto = str(headers.get("X-Forwarded-Proto") or "").split(",", 1)[0].strip().lower()
    if raw_proto not in {"http", "https"}:
        raw_proto = "https" if host.lower().endswith(".trycloudflare.com") else "http"
    return f"{raw_proto}://{host}".rstrip("/")


def _public_config_url_posture_v0(public_base_url: str) -> str:
    parsed = urlparse(public_base_url)
    host = str(parsed.hostname or "").lower()
    if host.endswith(".trycloudflare.com"):
        return "session_stable_quick_tunnel"
    if parsed.scheme == "https" and host not in {"localhost", "127.0.0.1", "::1"}:
        return "stable_named_url"
    return "local_loopback"


def _lp_duration_risk_policy_name_v0(policy: Any | None) -> str:
    if policy is None:
        return "none"
    if isinstance(policy, str):
        value = policy.strip()
        return value if value else "none"
    return "zeno-oracle"


def _lp_duration_risk_policy_from_name_v0(policy_name: Any) -> Any | None:
    if policy_name is None:
        return None
    if not isinstance(policy_name, str):
        raise ValueError("lp_duration_risk_policy must be a string")
    value = policy_name.strip()
    if value in {"", "none"}:
        return None
    if value == "zeno-oracle":
        from src.integration.zeno_oracle_fail_closed_config import (  # pylint: disable=import-outside-toplevel
            ZENO_ORACLE_LP_DURATION_RISK_POLICY,
        )

        return ZENO_ORACLE_LP_DURATION_RISK_POLICY
    raise ValueError(f"unsupported LP duration-risk policy: {value}")


def _public_network_config_for_request_v0(
    *,
    node_status: Mapping[str, Any],
    public_base_url: str,
    min_lp_position_age_seconds: int = 0,
    lp_duration_risk_policy: Any | None = None,
) -> dict[str, Any]:
    bundle_root = Path(str(node_status["bundle_root"]))
    public_base = public_base_url.rstrip("/")
    config = build_public_network_config_v0(
        bundle_root=bundle_root,
        mirror_base_url=f"{public_base}/ledger-bundle/",
        writer_urls=[public_base],
        peer_urls=[public_base],
        poll_seconds=1,
        node_port=8788,
        min_lp_position_age_seconds=min_lp_position_age_seconds,
        lp_duration_risk_policy=_lp_duration_risk_policy_name_v0(lp_duration_risk_policy),
    )
    config = {
        **config,
        "public_config_url": f"{public_base}/public_network_config.json",
        "public_config_url_posture": _public_config_url_posture_v0(public_base),
        "ui_url": public_base,
        "fake_value_public_testnet": True,
        "production_security_claim": False,
    }
    return {**config, "network_config_hash": _public_network_config_hash_v0(config)}


def make_node_http_server_v0(
    *,
    data_dir: Path,
    host: str,
    port: int,
    enable_testnet_intake: bool = False,
    enable_testnet_faucet: bool = False,
    expose_testnet_faucet_http: bool = False,
    allow_unauthenticated_testnet_writes: bool = False,
    min_lp_position_age_seconds: int = 0,
    lp_duration_risk_policy: Any | None = None,
    submit_peer_url: str | None = None,
    write_auth_token: str | None = None,
    submit_peer_auth_token: str | None = None,
    peer_urls: list[str] | None = None,
) -> ThreadingHTTPServer:
    """Create a small read-only HTTP server for node status artifacts."""

    if allow_unauthenticated_testnet_writes and host not in {"127.0.0.1", "localhost", "::1"}:
        raise ValueError("allow_unauthenticated_testnet_writes is only allowed on loopback binds")

    root = data_dir.resolve()
    append_lock = threading.Lock()
    mutation_enabled = enable_testnet_intake or enable_testnet_faucet
    write_auth_required = bool(
        mutation_enabled and (write_auth_token is not None or not allow_unauthenticated_testnet_writes)
    )

    class Handler(BaseHTTPRequestHandler):
        server_version = "ZenoLedgerNode/0"

        def _send_json(self, value: object, *, status: HTTPStatus = HTTPStatus.OK) -> None:
            payload = json.dumps(value, indent=2, sort_keys=True).encode("utf-8") + b"\n"
            self.send_response(int(status))
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(payload)))
            self.end_headers()
            self.wfile.write(payload)

        def _send_bytes(
            self,
            payload: bytes,
            *,
            status: HTTPStatus = HTTPStatus.OK,
            content_type: str = "application/octet-stream",
        ) -> None:
            self.send_response(int(status))
            self.send_header("Content-Type", content_type)
            self.send_header("Content-Length", str(len(payload)))
            self.end_headers()
            self.wfile.write(payload)

        def _require_write_auth(self) -> bool:
            if write_auth_token is None and allow_unauthenticated_testnet_writes:
                return True
            if write_auth_token is None:
                self._send_json(
                    build_rejection_report_v0(
                        BAD_AUTH,
                        "unauthorized",
                        error="write_auth_required",
                        path=self.path.split("?", 1)[0],
                    ),
                    status=HTTPStatus.UNAUTHORIZED,
                )
                return False
            expected = f"Bearer {write_auth_token}"
            got = self.headers.get("Authorization", "")
            if hmac.compare_digest(got, expected):
                return True
            self._send_json(
                build_rejection_report_v0(
                    BAD_AUTH,
                    "unauthorized",
                    error="unauthorized",
                    path=self.path.split("?", 1)[0],
                ),
                status=HTTPStatus.UNAUTHORIZED,
            )
            return False

        def do_GET(self) -> None:  # noqa: N802
            try:
                status = load_node_status_v0(root)
                parsed_url = urlparse(self.path)
                request_path = parsed_url.path
                query = parse_qs(parsed_url.query, keep_blank_values=False)
                parts = [part for part in request_path.split("/") if part]
                if request_path == "/public_network_config.json":
                    self._send_json(
                        _public_network_config_for_request_v0(
                            node_status=status,
                            public_base_url=_public_base_url_from_headers_v0(self.headers),
                            min_lp_position_age_seconds=min_lp_position_age_seconds,
                            lp_duration_risk_policy=lp_duration_risk_policy,
                        )
                    )
                    return
                if request_path.startswith("/ledger-bundle/"):
                    rel = unquote(request_path[len("/ledger-bundle/") :]).lstrip("/")
                    if not _is_safe_relative(rel):
                        self._send_json({"ok": False, "error": "unsafe_bundle_path"}, status=HTTPStatus.BAD_REQUEST)
                        return
                    bundle_root = Path(str(status["bundle_root"])).resolve()
                    artifact_rel = _public_bundle_artifact_rel_for_request_v0(bundle_root, rel)
                    if artifact_rel is None:
                        self._send_json({"ok": False, "error": "bundle_artifact_not_public"}, status=HTTPStatus.NOT_FOUND)
                        return
                    # rel is checked as a safe relative path and constrained below bundle_root.
                    path = (bundle_root / artifact_rel).resolve()
                    try:
                        path.relative_to(bundle_root)
                    except ValueError:
                        self._send_json({"ok": False, "error": "unsafe_bundle_path"}, status=HTTPStatus.BAD_REQUEST)
                        return
                    # path is confirmed to remain below bundle_root before filesystem access.
                    if not _artifact_is_file_v0(path):
                        self._send_json({"ok": False, "error": "bundle_artifact_missing"}, status=HTTPStatus.NOT_FOUND)
                        return
                    # path is a confirmed file below bundle_root and size-capped before response.
                    data = _read_artifact_bytes_v0(path)
                    max_bytes = (
                        MAX_REMOTE_BUNDLE_ARCHIVE_BYTES
                        if artifact_rel == PUBLIC_BUNDLE_ARCHIVE_NAME
                        else MAX_REMOTE_ARTIFACT_BYTES
                    )
                    if len(data) > max_bytes:
                        self._send_json(
                            {"ok": False, "error": "bundle_artifact_too_large"},
                            status=HTTPStatus.REQUEST_ENTITY_TOO_LARGE,
                        )
                        return
                    content_type = "application/gzip" if artifact_rel == PUBLIC_BUNDLE_ARCHIVE_NAME else "application/json"
                    self._send_bytes(data, content_type=content_type)
                    return
                if len(parts) == 3 and parts[0] == "live" and parts[1] in {"header", "body", "checkpoint", "snapshot"}:
                    try:
                        height = int(parts[2])
                    except ValueError:
                        self._send_json({"ok": False, "error": "invalid_height"}, status=HTTPStatus.BAD_REQUEST)
                        return
                    artifact_path = _live_artifact_path(data_dir=root, kind=parts[1], height=height)
                    if not artifact_path.is_file():
                        self._send_json({"ok": False, "error": "live_artifact_missing"}, status=HTTPStatus.NOT_FOUND)
                    else:
                        self._send_json(_load_json_object(artifact_path))
                    return
                if request_path in {"/", "/health"}:
                    self._send_json(
                        {
                            "ok": status["ok"],
                            "node_id": status["node_id"],
                            "node_status_hash": status["node_status_hash"],
                            "latest_height": status["latest_height"],
                        }
                    )
                    return
                if request_path == "/status":
                    self._send_json(status)
                    return
                if request_path == "/features":
                    self._send_json(
                        {
                            "feature_suite_hash": status["feature_suite_hash"],
                            "covered_feature_count": status["covered_feature_count"],
                            "covered_features": status["covered_features"],
                            "required_features": status["required_features"],
                        }
                    )
                    return
                if request_path == "/tokens":
                    self._send_json(
                        {
                            "token_symbol": status["token_symbol"],
                            "token_distribution": status.get("token_distribution", {}),
                            "tokenomics_posture": status.get("tokenomics_posture", {}),
                            "token_posture": status["token_posture"],
                            "test_token_catalog": status["test_token_catalog"],
                            "testnet_faucet_posture": status["testnet_faucet_posture"],
                        }
                    )
                    return
                if request_path == "/network":
                    self._send_json(
                        {
                            "schema": "zenodex.zeno_ledger.node_network_status.v0",
                            "ok": status["ok"],
                            "node_id": status["node_id"],
                            "node_role": status["node_role"],
                            "network_id": status["network_id"],
                            "chain_id": status["chain_id"],
                            "bootstrap_latest_height": status["latest_height"],
                            "local_tip": _local_tip_v0(data_dir=root, node_status=status),
                            "peer_urls": list(peer_urls or []),
                            "peer_count": len(peer_urls or []),
                            "submit_peer_url": submit_peer_url,
                            "capabilities": {
                                "testnet_intake_enabled": enable_testnet_intake,
                                "testnet_faucet_enabled": enable_testnet_faucet,
                                "testnet_faucet_http_exposed": expose_testnet_faucet_http,
                                "write_auth_required": write_auth_required,
                                "unauthenticated_testnet_writes_allowed": allow_unauthenticated_testnet_writes,
                                "submission_forwarding_enabled": submit_peer_url is not None,
                                "submit_peer_auth_configured": submit_peer_auth_token is not None,
                            },
                        }
                    )
                    return
                if request_path == "/api/pools":
                    account_raw = ""
                    for key in ("account", "account_pubkey", "accountPubkey", "pubkey"):
                        values = query.get(key)
                        if values:
                            account_raw = values[0]
                            break
                    account_pubkey = (
                        _require_pubkey_v0(account_raw, name="account")
                        if isinstance(account_raw, str) and account_raw.strip()
                        else None
                    )
                    self._send_json(_ui_pools_response_v0(data_dir=root, node_status=status, account_pubkey=account_pubkey))
                    return
                if request_path == "/api/dex/snapshot":
                    latest_height, snapshot = _latest_snapshot_for_ui_v0(data_dir=root, node_status=status)
                    self._send_json({"ok": True, "latest_height": latest_height, "snapshot": snapshot})
                    return
                if request_path == "/api/tokenomics/status":
                    self._send_json(_ui_tokenomics_response_v0(data_dir=root, node_status=status))
                    return
                if request_path == "/live":
                    live_path = root / "live_state.json"
                    if not live_path.is_file():
                        self._send_json({"ok": True, "live": False})
                    else:
                        self._send_json({"ok": True, "live": True, "state": _load_live_state_v0(root, node_status=status)})
                    return
                if request_path == "/attestation":
                    attestation = _load_optional_json(status.get("operator_attestation_path"))
                    if attestation is None:
                        self._send_json({"ok": False, "error": "attestation_missing"}, status=HTTPStatus.NOT_FOUND)
                    else:
                        self._send_json(attestation)
                    return
                if request_path == "/testnet-status":
                    testnet_status = _load_optional_json(status.get("combined_testnet_status_path"))
                    if testnet_status is None:
                        self._send_json({"ok": False, "error": "testnet_status_missing"}, status=HTTPStatus.NOT_FOUND)
                    else:
                        self._send_json(testnet_status)
                    return
                self._send_json({"ok": False, "error": "not_found"}, status=HTTPStatus.NOT_FOUND)
            except Exception as exc:
                self._send_json({"ok": False, "error": str(exc)}, status=HTTPStatus.INTERNAL_SERVER_ERROR)

        def do_POST(self) -> None:  # noqa: N802
            try:
                request_path = self.path.split("?", 1)[0]
                if request_path in {"/api/swap", "/api/liquidity/create", "/api/liquidity/add", "/api/liquidity/remove"}:
                    if not self._require_write_auth():
                        return
                    if not enable_testnet_intake:
                        self._send_json({"ok": False, "error": "testnet_intake_disabled"}, status=HTTPStatus.FORBIDDEN)
                        return
                    payload = _read_http_json_body(self)
                    if submit_peer_url:
                        peer_path = request_path.lstrip("/")
                        report, peer_status = _post_json_url(
                            urljoin(submit_peer_url.rstrip("/") + "/", peer_path),
                            payload,
                            bearer_token=submit_peer_auth_token,
                        )
                        self._send_json({**report, "forwarded_to": submit_peer_url}, status=peer_status)
                        return
                    time_ms = payload.get("time_ms", payload.get("timeMs"))
                    if time_ms is None:
                        time_ms = int(time.time() * 1000)
                    if not isinstance(time_ms, int) or isinstance(time_ms, bool) or time_ms < 0:
                        self._send_json({"ok": False, "error": "time_ms_must_be_nonnegative_int"}, status=HTTPStatus.BAD_REQUEST)
                        return
                    status = load_node_status_v0(root)
                    if request_path == "/api/swap":
                        tx = _ui_swap_tx_v0(data_dir=root, node_status=status, payload=payload, time_ms=int(time_ms))
                    elif request_path == "/api/liquidity/create":
                        tx = _ui_create_pool_tx_v0(
                            data_dir=root,
                            node_status=status,
                            payload=payload,
                            time_ms=int(time_ms),
                        )
                    else:
                        tx = _ui_liquidity_tx_v0(
                            data_dir=root,
                            node_status=status,
                            payload=payload,
                            time_ms=int(time_ms),
                            kind="ADD_LIQUIDITY" if request_path == "/api/liquidity/add" else "REMOVE_LIQUIDITY",
                            min_lp_position_age_seconds=min_lp_position_age_seconds,
                            lp_duration_risk_policy=lp_duration_risk_policy,
                        )
                    with append_lock:
                        report = append_dex_transaction_v0(
                            data_dir=root,
                            tx=tx,
                            time_ms=int(time_ms),
                            min_lp_position_age_seconds=min_lp_position_age_seconds,
                            lp_duration_risk_policy=lp_duration_risk_policy,
                        )
                    receipt = report.get("receipt")
                    accepted = bool(isinstance(receipt, Mapping) and receipt.get("accepted") is True)
                    response = {
                        **report,
                        "ok": accepted,
                        "txHash": report["tx_hash"],
                        "tx_hash": report["tx_hash"],
                        "tx_accepted": accepted,
                        "receipt": receipt,
                    }
                    self._send_json(response, status=HTTPStatus.OK if accepted else HTTPStatus.BAD_REQUEST)
                    return
                if request_path in {"/api/tokenomics/active-participant/claim", "/api/tokenomics/claim"}:
                    if not self._require_write_auth():
                        return
                    if not enable_testnet_intake:
                        self._send_json({"ok": False, "error": "testnet_intake_disabled"}, status=HTTPStatus.FORBIDDEN)
                        return
                    payload = _read_http_json_body(self)
                    if submit_peer_url:
                        peer_path = request_path.lstrip("/")
                        report, peer_status = _post_json_url(
                            urljoin(submit_peer_url.rstrip("/") + "/", peer_path),
                            payload,
                            bearer_token=submit_peer_auth_token,
                        )
                        self._send_json({**report, "forwarded_to": submit_peer_url}, status=peer_status)
                        return
                    time_ms = payload.get("time_ms", payload.get("timeMs"))
                    if time_ms is None:
                        time_ms = int(time.time() * 1000)
                    if not isinstance(time_ms, int) or isinstance(time_ms, bool) or time_ms < 0:
                        self._send_json({"ok": False, "error": "time_ms_must_be_nonnegative_int"}, status=HTTPStatus.BAD_REQUEST)
                        return
                    with append_lock:
                        report = append_tokenomics_reward_claim_v0(
                            data_dir=root,
                            payload=payload,
                            time_ms=int(time_ms),
                        )
                    self._send_json(report)
                    return
                if request_path == "/tx":
                    if not self._require_write_auth():
                        return
                    if not enable_testnet_intake:
                        self._send_json({"ok": False, "error": "testnet_intake_disabled"}, status=HTTPStatus.FORBIDDEN)
                        return
                    payload = _read_http_json_body(self)
                    if submit_peer_url:
                        report, peer_status = _post_json_url(
                            urljoin(submit_peer_url.rstrip("/") + "/", "tx"),
                            payload,
                            bearer_token=submit_peer_auth_token,
                        )
                        self._send_json({**report, "forwarded_to": submit_peer_url}, status=peer_status)
                        return
                    tx_raw = payload.get("tx", payload)
                    if not isinstance(tx_raw, Mapping):
                        self._send_json({"ok": False, "error": "tx_must_be_object"}, status=HTTPStatus.BAD_REQUEST)
                        return
                    time_ms = payload.get("time_ms")
                    if time_ms is None:
                        time_ms = int(time.time() * 1000)
                    if not isinstance(time_ms, int) or isinstance(time_ms, bool) or time_ms < 0:
                        self._send_json({"ok": False, "error": "time_ms_must_be_nonnegative_int"}, status=HTTPStatus.BAD_REQUEST)
                        return
                    with append_lock:
                        report = append_dex_transaction_v0(
                            data_dir=root,
                            tx=tx_raw,
                            time_ms=int(time_ms),
                            min_lp_position_age_seconds=min_lp_position_age_seconds,
                            lp_duration_risk_policy=lp_duration_risk_policy,
                        )
                    self._send_json(report, status=HTTPStatus.OK if report["ok"] else HTTPStatus.BAD_REQUEST)
                    return
                if request_path == "/faucet":
                    if not self._require_write_auth():
                        return
                    if not enable_testnet_faucet:
                        self._send_json({"ok": False, "error": "testnet_faucet_disabled"}, status=HTTPStatus.FORBIDDEN)
                        return
                    payload = _read_http_json_body(self)
                    if not expose_testnet_faucet_http:
                        self._send_json(
                            {
                                "ok": False,
                                "error": "testnet_faucet_http_not_exposed",
                                "production_security_claim": False,
                            },
                            status=HTTPStatus.FORBIDDEN,
                        )
                        return
                    if not _local_fixture_faucet_ack_v0(payload):
                        self._send_json(
                            {
                                "ok": False,
                                "error": "testnet_faucet_fixture_ack_required",
                                "production_security_claim": False,
                            },
                            status=HTTPStatus.FORBIDDEN,
                        )
                        return
                    if submit_peer_url:
                        report, peer_status = _post_json_url(
                            urljoin(submit_peer_url.rstrip("/") + "/", "faucet"),
                            payload,
                            bearer_token=submit_peer_auth_token,
                        )
                        self._send_json({**report, "forwarded_to": submit_peer_url}, status=peer_status)
                        return
                    time_ms = payload.get("time_ms")
                    if time_ms is None:
                        time_ms = int(time.time() * 1000)
                    if not isinstance(time_ms, int) or isinstance(time_ms, bool) or time_ms < 0:
                        self._send_json({"ok": False, "error": "time_ms_must_be_nonnegative_int"}, status=HTTPStatus.BAD_REQUEST)
                        return
                    with append_lock:
                        report = append_testnet_faucet_v0(
                            data_dir=root,
                            to_pubkey=str(payload.get("to_pubkey", "")),
                            asset=str(payload.get("asset", "")),
                            amount=_require_positive_amount_v0(
                                payload.get("amount"),
                                name="amount",
                                maximum=MAX_TESTNET_FAUCET_AMOUNT,
                            ),
                            tx_id=str(payload.get("tx_id", "node-testnet-faucet-v0")),
                            time_ms=int(time_ms),
                        )
                    self._send_json(report)
                    return
                self._send_json({"ok": False, "error": "not_found"}, status=HTTPStatus.NOT_FOUND)
            except _HttpRejectedError as exc:
                self._send_json(exc.report, status=exc.status)
            except Exception as exc:
                self._send_json({"ok": False, "error": str(exc)}, status=HTTPStatus.BAD_REQUEST)

        def log_message(self, format: str, *args: object) -> None:
            return

    return ThreadingHTTPServer((host, port), Handler)


def _record_peer_follow_error_log_due_v0(
    last_logged: dict[str, OrderedDict[str, float]],
    *,
    peer_url: str,
    error_text: str,
    now: float,
    min_interval_s: float = 60.0,
    cap_per_peer: int = PEER_FOLLOW_ERROR_LOG_CAP_PER_PEER,
) -> bool:
    """Return True when a peer-follow error should be logged.

    The table is bounded per peer. Error strings can contain changing detail,
    so a plain key per error text can grow forever in a long-lived follower.
    """
    peer_table = last_logged.setdefault(peer_url, OrderedDict())
    signature = hashlib.sha256(error_text.encode("utf-8", errors="replace")).hexdigest()
    last_seen = peer_table.get(signature)
    peer_table[signature] = float(now)
    peer_table.move_to_end(signature)
    while len(peer_table) > int(cap_per_peer):
        peer_table.popitem(last=False)
    return bool(last_seen is None or now - float(last_seen) >= min_interval_s)


def _start_peer_follow_loop(
    *,
    data_dir: Path,
    peer_urls: list[str],
    poll_seconds: int,
    min_lp_position_age_seconds: int = 0,
    lp_duration_risk_policy: Any | None = None,
) -> None:
    if not peer_urls or poll_seconds <= 0:
        return

    def _loop() -> None:
        # Per-peer rate limit so we don't spam stderr when a peer is down for
        # minutes. The helper keeps bounded LRU state per peer even when error
        # strings carry varying timestamps, ports, or retry counters.
        last_logged: dict[str, OrderedDict[str, float]] = {}
        while True:
            for peer_url in peer_urls:
                try:
                    pull_live_from_peer_v0(
                        data_dir=data_dir,
                        peer_url=peer_url,
                        min_lp_position_age_seconds=min_lp_position_age_seconds,
                        lp_duration_risk_policy=lp_duration_risk_policy,
                    )
                except Exception as exc:
                    error_text = str(exc)
                    now = time.monotonic()
                    if _record_peer_follow_error_log_due_v0(
                        last_logged,
                        peer_url=peer_url,
                        error_text=error_text,
                        now=now,
                    ):
                        try:
                            print(
                                json.dumps(
                                    {
                                        "schema": "zenodex.zeno_ledger.node_peer_pull_error.v0",
                                        "ok": False,
                                        "peer_url": peer_url,
                                        "error": error_text,
                                    },
                                    sort_keys=True,
                                ),
                                file=sys.stderr,
                                flush=True,
                            )
                        except Exception:
                            pass
            time.sleep(poll_seconds)

    thread = threading.Thread(target=_loop, daemon=True)
    thread.start()


def serve_node_v0(
    *,
    data_dir: Path,
    host: str,
    port: int,
    peer_urls: list[str] | None = None,
    poll_seconds: int = 0,
    enable_testnet_intake: bool = False,
    enable_testnet_faucet: bool = False,
    expose_testnet_faucet_http: bool = False,
    allow_unauthenticated_testnet_writes: bool = False,
    min_lp_position_age_seconds: int = 0,
    lp_duration_risk_policy: Any | None = None,
    submit_peer_url: str | None = None,
    write_auth_token: str | None = None,
    submit_peer_auth_token: str | None = None,
) -> None:
    _start_peer_follow_loop(
        data_dir=data_dir,
        peer_urls=list(peer_urls or []),
        poll_seconds=poll_seconds,
        min_lp_position_age_seconds=min_lp_position_age_seconds,
        lp_duration_risk_policy=lp_duration_risk_policy,
    )
    server = make_node_http_server_v0(
        data_dir=data_dir,
        host=host,
        port=port,
        enable_testnet_intake=enable_testnet_intake,
        enable_testnet_faucet=enable_testnet_faucet,
        expose_testnet_faucet_http=expose_testnet_faucet_http,
        allow_unauthenticated_testnet_writes=allow_unauthenticated_testnet_writes,
        min_lp_position_age_seconds=min_lp_position_age_seconds,
        lp_duration_risk_policy=lp_duration_risk_policy,
        submit_peer_url=submit_peer_url,
        write_auth_token=write_auth_token,
        submit_peer_auth_token=submit_peer_auth_token,
        peer_urls=list(peer_urls or []),
    )
    server_address = server.server_address
    raw_address = server_address[0]
    address = raw_address.decode("utf-8") if isinstance(raw_address, bytes) else str(raw_address)
    actual_port = int(server_address[1])
    print(
        json.dumps(
            {
                "schema": "zenodex.zeno_ledger.node_server_ready.v0",
                "ok": True,
                "host": address,
                "port": actual_port,
                "peer_count": len(peer_urls or []),
                "poll_seconds": poll_seconds,
                "testnet_intake_enabled": enable_testnet_intake,
                "testnet_faucet_enabled": enable_testnet_faucet,
                "testnet_faucet_http_exposed": expose_testnet_faucet_http,
                "write_auth_required": bool(
                    (enable_testnet_intake or enable_testnet_faucet)
                    and (write_auth_token is not None or not allow_unauthenticated_testnet_writes)
                ),
                "unauthenticated_testnet_writes_allowed": allow_unauthenticated_testnet_writes,
                "submit_peer_url": submit_peer_url,
                "submit_peer_auth_configured": submit_peer_auth_token is not None,
                "status_url": f"http://{address}:{actual_port}/status",
            },
            indent=2,
            sort_keys=True,
        ),
        flush=True,
    )
    server.serve_forever()


def preflight_node_join_config_v0(
    *,
    config_path: Path,
    check_port: bool = True,
    strict_exposure: bool = False,
    public_operator: bool = False,
) -> dict[str, Any]:
    """Validate an operator join config before sync/replay/serve side effects."""

    errors: list[str] = []
    warnings: list[str] = []
    checks: dict[str, bool] = {}
    try:
        config = dict(_load_json_object(config_path))
    except Exception as exc:
        return {
            "schema": NODE_PREFLIGHT_REPORT_SCHEMA,
            "ok": False,
            "status": "rejected",
            "config_path": str(config_path),
            "errors": [str(exc)],
            "warnings": [],
            "checks": {},
        }

    if config.get("schema") not in {None, NODE_JOIN_CONFIG_SCHEMA}:
        errors.append("node join config schema mismatch")
    checks["schema"] = not errors

    node_id = str(config.get("node_id", "")).strip()
    if node_id == "":
        errors.append("node_id is required")
    checks["node_id"] = node_id != ""

    data_dir_ok = False
    data_dir_parent_ok = False
    try:
        data_dir = _as_path(config.get("data_dir"), name="data_dir")
        data_dir_ok = True
        data_dir_parent_ok = data_dir.parent.exists()
        if data_dir.exists() and not data_dir.is_dir():
            errors.append("data_dir exists but is not a directory")
        if not data_dir_parent_ok:
            warnings.append(f"data_dir parent does not exist yet: {data_dir.parent}")
    except Exception as exc:
        errors.append(str(exc))
        data_dir = None
    checks["data_dir"] = data_dir_ok
    checks["data_dir_parent"] = data_dir_parent_ok

    bundle_root_ok = False
    base_url = config.get("base_url")
    if base_url is not None:
        if not isinstance(base_url, str) or not _is_http_url(base_url):
            errors.append("base_url must be an http(s) URL without embedded credentials")
        else:
            bundle_root_ok = True
    try:
        bundle_root = _as_path(config.get("bundle_root"), name="bundle_root")
        if base_url is None:
            _read_public_manifest(bundle_root)
            bundle_root_ok = True
        elif bundle_root.is_file():
            errors.append("bundle_root must not be a file")
    except Exception as exc:
        errors.append(str(exc))
    checks["bundle_source"] = bundle_root_ok

    peer_urls_ok = True
    try:
        peer_urls = _as_string_list(config.get("peer_urls"), name="peer_urls")
    except Exception as exc:
        errors.append(str(exc))
        peer_urls = []
        peer_urls_ok = False
    for peer_url in peer_urls:
        if not _is_http_url(peer_url):
            errors.append(f"peer_url must be an http(s) URL without embedded credentials: {peer_url}")
            peer_urls_ok = False
    checks["peer_urls"] = peer_urls_ok

    submit_peer_url = config.get("submit_peer_url")
    if submit_peer_url is not None and (not isinstance(submit_peer_url, str) or not _is_http_url(submit_peer_url)):
        errors.append("submit_peer_url must be an http(s) URL without embedded credentials")
        checks["submit_peer_url"] = False
    else:
        checks["submit_peer_url"] = True

    write_auth_inline = config.get("write_auth_token") is not None
    submit_peer_auth_inline = config.get("submit_peer_auth_token") is not None
    write_auth_env_configured = (
        isinstance(config.get("write_auth_token_env"), str)
        and config.get("write_auth_token_env") != ""
    )
    submit_peer_auth_env_configured = (
        isinstance(config.get("submit_peer_auth_token_env"), str)
        and config.get("submit_peer_auth_token_env") != ""
    )
    try:
        write_auth_token = _auth_token_from_config(
            config,
            token_key="write_auth_token",
            env_key="write_auth_token_env",
        )
    except Exception as exc:
        errors.append(str(exc))
        write_auth_token = None
    try:
        submit_peer_auth_token = _auth_token_from_config(
            config,
            token_key="submit_peer_auth_token",
            env_key="submit_peer_auth_token_env",
        )
    except Exception as exc:
        errors.append(str(exc))
        submit_peer_auth_token = None
    checks["write_auth"] = write_auth_token is not None
    checks["submit_peer_auth"] = submit_peer_url is None or submit_peer_auth_token is not None
    checks["inline_auth_tokens_absent"] = not (write_auth_inline or submit_peer_auth_inline)
    if write_auth_inline or submit_peer_auth_inline:
        warnings.append("inline auth tokens are present in the config; prefer *_auth_token_env for operator configs")

    serve = config.get("serve") is True
    checks["serve_flag"] = isinstance(config.get("serve"), bool) or config.get("serve") is None
    if not checks["serve_flag"]:
        errors.append("serve must be a boolean when present")

    host = str(config.get("host", "127.0.0.1"))
    raw_port = config.get("port", 8787)
    raw_poll_seconds = config.get("poll_seconds", 0)
    port = int(raw_port) if isinstance(raw_port, int) and not isinstance(raw_port, bool) else -1
    poll_seconds = (
        int(raw_poll_seconds)
        if isinstance(raw_poll_seconds, int) and not isinstance(raw_poll_seconds, bool)
        else -1
    )
    checks["port_range"] = 0 < port <= 65535
    checks["poll_seconds"] = poll_seconds >= 0
    if not checks["port_range"]:
        errors.append("port must be an integer in 1..65535")
    if not checks["poll_seconds"]:
        errors.append("poll_seconds must be a nonnegative integer")
    if serve and check_port and checks["port_range"]:
        port_available = _tcp_port_available(host, port)
        checks["port_available"] = port_available
        if not port_available:
            errors.append(f"port is not available for bind: {host}:{port}")
    elif serve:
        checks["port_available"] = True

    testnet_mutation_enabled = (
        serve
        and (config.get("enable_testnet_faucet") is True or config.get("enable_testnet_intake") is True)
    )
    public_bind = serve and host in {"0.0.0.0", "::"}
    expose_testnet_faucet_http_raw = config.get("expose_testnet_faucet_http")
    expose_testnet_faucet_http = expose_testnet_faucet_http_raw is True
    checks["expose_testnet_faucet_http"] = expose_testnet_faucet_http
    checks["expose_testnet_faucet_http_shape"] = (
        expose_testnet_faucet_http_raw is None or isinstance(expose_testnet_faucet_http_raw, bool)
    )
    if not checks["expose_testnet_faucet_http_shape"]:
        errors.append("expose_testnet_faucet_http must be a boolean when present")
    if expose_testnet_faucet_http and config.get("enable_testnet_faucet") is not True:
        errors.append("expose_testnet_faucet_http requires enable_testnet_faucet")
    allow_unauthenticated_testnet_writes_raw = config.get("allow_unauthenticated_testnet_writes")
    allow_unauthenticated_testnet_writes = allow_unauthenticated_testnet_writes_raw is True
    checks["allow_unauthenticated_testnet_writes"] = allow_unauthenticated_testnet_writes
    checks["allow_unauthenticated_testnet_writes_shape"] = (
        allow_unauthenticated_testnet_writes_raw is None
        or isinstance(allow_unauthenticated_testnet_writes_raw, bool)
    )
    if not checks["allow_unauthenticated_testnet_writes_shape"]:
        errors.append("allow_unauthenticated_testnet_writes must be a boolean when present")
    if public_bind:
        message = "serve host exposes the node on all interfaces; place it behind firewall/auth controls"
        warnings.append(message)
        if strict_exposure:
            errors.append(f"strict_exposure: {message}")
    if allow_unauthenticated_testnet_writes and public_bind:
        errors.append("allow_unauthenticated_testnet_writes is only allowed on loopback binds")
    if config.get("enable_testnet_faucet") is True:
        message = "testnet faucet is enabled; never expose this on a real-value network"
        warnings.append(message)
        if strict_exposure and public_bind:
            errors.append(f"strict_exposure: {message}")
    if expose_testnet_faucet_http:
        message = "HTTP testnet faucet is exposed; use only for explicit local fixture funding"
        warnings.append(message)
        if strict_exposure and public_bind:
            errors.append(f"strict_exposure: {message}")
    if config.get("enable_testnet_intake") is True and serve:
        message = "testnet transaction intake is enabled; this endpoint accepts unsigned fixture traffic"
        warnings.append(message)
        if strict_exposure and public_bind:
            errors.append(f"strict_exposure: {message}")
    if testnet_mutation_enabled and write_auth_token is None:
        if allow_unauthenticated_testnet_writes:
            warnings.append("unauthenticated testnet writes are explicitly enabled for this local node")
        else:
            errors.append("enabled testnet mutation endpoints require write_auth_token_env or write_auth_token")
    if submit_peer_url is not None and submit_peer_auth_token is None:
        warnings.append("submit_peer_auth_token_env is not configured; forwarded writes will be unauthenticated")
    if config.get("enable_testnet_faucet") is True and config.get("enable_testnet_intake") is not True:
        warnings.append("faucet is enabled while testnet intake is disabled; faucet requests will not be useful")

    checks["public_operator_bind"] = not public_operator or not public_bind
    checks["public_operator_inline_auth"] = not public_operator or not (write_auth_inline or submit_peer_auth_inline)
    checks["public_operator_write_auth_env"] = (
        not public_operator
        or not testnet_mutation_enabled
        or write_auth_env_configured
    )
    checks["public_operator_submit_peer_auth_env"] = (
        not public_operator
        or submit_peer_url is None
        or submit_peer_auth_env_configured
    )
    if public_operator:
        if public_bind:
            errors.append("public_operator: serve host must bind locally behind an authenticated reverse proxy")
            if testnet_mutation_enabled:
                errors.append("public_operator: public binds must not expose testnet faucet or intake endpoints")
            if expose_testnet_faucet_http:
                errors.append("public_operator: public binds must not expose HTTP testnet faucet")
        if write_auth_inline or submit_peer_auth_inline:
            errors.append("public_operator: inline auth tokens are forbidden; use *_auth_token_env")
        if testnet_mutation_enabled and not write_auth_env_configured:
            errors.append("public_operator: enabled mutation endpoints require write_auth_token_env")
        if submit_peer_url is not None and not submit_peer_auth_env_configured:
            errors.append("public_operator: submit_peer_url requires submit_peer_auth_token_env")

    ok = not errors
    return {
        "schema": NODE_PREFLIGHT_REPORT_SCHEMA,
        "ok": ok,
        "status": "accepted" if ok else "rejected",
        "config_path": str(config_path),
        "node_id": node_id,
        "serve": serve,
        "host": host,
        "port": port,
        "peer_count": len(peer_urls),
        "check_port": check_port,
        "strict_exposure": strict_exposure,
        "public_operator": public_operator,
        "errors": errors,
        "warnings": warnings,
        "checks": checks,
    }


def join_public_node_from_config_v0(*, config_path: Path) -> dict[str, Any]:
    """Sync, verify, and optionally serve a node from one operator config."""

    config = dict(_load_json_object(config_path))
    if config.get("schema") not in {None, NODE_JOIN_CONFIG_SCHEMA}:
        raise ValueError("node join config schema mismatch")
    node_id = str(config.get("node_id", "")).strip()
    if node_id == "":
        raise ValueError("node_id is required")
    data_dir = _as_path(config.get("data_dir"), name="data_dir")
    bundle_root: Path
    sync_report: dict[str, Any] | None = None
    base_url = config.get("base_url")
    if base_url is not None:
        if not isinstance(base_url, str) or base_url == "":
            raise ValueError("base_url must be a non-empty string")
        bundle_root = _as_path(config.get("bundle_root"), name="bundle_root")
        bundle_archive_url = config.get("bundle_archive_url")
        bundle_archive_sha256 = config.get("bundle_archive_sha256")
        if bundle_archive_url is not None and not isinstance(bundle_archive_url, str):
            raise ValueError("bundle_archive_url must be a string")
        if bundle_archive_sha256 is not None and not isinstance(bundle_archive_sha256, str):
            raise ValueError("bundle_archive_sha256 must be a string")
        sync_report = sync_public_bundle_from_url_v0(
            base_url=base_url,
            out_dir=bundle_root,
            bundle_archive_url=bundle_archive_url,
            bundle_archive_sha256=bundle_archive_sha256,
        )
    else:
        bundle_root = _as_path(config.get("bundle_root"), name="bundle_root")
        _read_public_manifest(bundle_root)

    peer_watcher_attestations = _as_path_list(
        config.get("peer_watcher_attestation_paths"),
        name="peer_watcher_attestation_paths",
    )
    if not peer_watcher_attestations:
        default_attestation = bundle_root / "bootstrap" / "watcher_attestations" / "bootstrap_range_1_5.json"
        if default_attestation.is_file():
            peer_watcher_attestations = [default_attestation]

    observed_time_ms = config.get("observed_time_ms")
    if observed_time_ms is not None and (not isinstance(observed_time_ms, int) or isinstance(observed_time_ms, bool)):
        raise ValueError("observed_time_ms must be an integer")
    run_report = run_node_once_v0(
        bundle_root=bundle_root,
        node_id=node_id,
        data_dir=data_dir,
        observed_time_ms=observed_time_ms,
        peer_watcher_attestation_paths=peer_watcher_attestations,
    )
    peer_urls = _as_string_list(config.get("peer_urls"), name="peer_urls")
    peer_check = check_peer_status_v0(data_dir=data_dir, peer_urls=peer_urls) if peer_urls else None
    ok = (
        run_report.get("ok") is True
        and (sync_report is None or sync_report.get("ok") is True)
        and (peer_check is None or peer_check.get("ok") is True)
    )
    report = {
        "schema": NODE_JOIN_REPORT_SCHEMA,
        "ok": ok,
        "status": "accepted",
        "config_path": str(config_path),
        "node_id": node_id,
        "bundle_root": str(bundle_root),
        "data_dir": str(data_dir),
        "submit_peer_url": config.get("submit_peer_url"),
        "sync_report": sync_report,
        "run_report": run_report,
        "peer_check": peer_check,
        "peer_count": len(peer_urls),
    }
    if peer_check is not None and peer_check.get("ok") is not True:
        report["status"] = "peer_check_rejected"
    elif report["ok"] is True:
        report["status"] = "accepted"
    else:
        report["status"] = "rejected"
    _write_json(data_dir / "node_join_report.json", report)
    return report


def build_public_network_config_v0(
    *,
    bundle_root: Path,
    mirror_base_url: str,
    writer_urls: list[str],
    peer_urls: list[str],
    poll_seconds: int,
    node_port: int,
    min_lp_position_age_seconds: int = 0,
    lp_duration_risk_policy: str | None = None,
) -> dict[str, Any]:
    """Build a public operator config for joining a ZenoLedger testnet."""

    if not writer_urls:
        raise ValueError("at least one writer URL is required")
    if poll_seconds < 0:
        raise ValueError("poll_seconds must be nonnegative")
    if node_port <= 0 or node_port > 65535:
        raise ValueError("node_port must be a valid TCP port")
    if min_lp_position_age_seconds < 0:
        raise ValueError("min_lp_position_age_seconds must be nonnegative")
    lp_duration_risk_policy_name = _lp_duration_risk_policy_name_v0(lp_duration_risk_policy)
    public_manifest = _read_public_manifest(bundle_root)
    feature_suite = _read_feature_suite(bundle_root, public_manifest)
    config = {
        "schema": NODE_PUBLIC_NETWORK_CONFIG_SCHEMA,
        "ok": True,
        "status": "accepted",
        "network_id": public_manifest["network_id"],
        "chain_id": public_manifest["chain_id"],
        "token_symbol": public_manifest.get("token_symbol"),
        "token_distribution": dict(public_manifest.get("token_distribution", {})),
        "token_distribution_hash": public_manifest.get("token_distribution_hash"),
        "tokenomics_posture": dict(public_manifest.get("tokenomics_posture", {})),
        "mirror_base_url": mirror_base_url.rstrip("/") + "/",
        "writer_urls": _unique_strings(writer_urls),
        "peer_urls": _unique_strings([*writer_urls, *peer_urls]),
        "feature_suite_hash": feature_suite["feature_suite_hash"],
        "feature_count": feature_suite["feature_count"],
        "test_token_catalog": list(public_manifest.get("test_token_catalog", [])),
        "testnet_faucet_posture": dict(public_manifest.get("testnet_faucet_posture", {})),
        "recommended_node": {
            "host": "0.0.0.0",
            "port": node_port,
            "poll_seconds": poll_seconds,
            "enable_testnet_intake": True,
            "enable_testnet_faucet": True,
            "expose_testnet_faucet_http": False,
            "submit_peer_url": writer_urls[0],
            "min_lp_position_age_seconds": int(min_lp_position_age_seconds),
            "lp_duration_risk_policy": lp_duration_risk_policy_name,
        },
    }
    archive_path = _public_bundle_archive_path_v0(bundle_root)
    if archive_path.is_file():
        archive_size = archive_path.stat().st_size
        if archive_size <= MAX_REMOTE_BUNDLE_ARCHIVE_BYTES:
            config.update(
                {
                    "bundle_archive_url": urljoin(
                        mirror_base_url.rstrip("/") + "/",
                        PUBLIC_BUNDLE_ARCHIVE_NAME,
                    ),
                    "bundle_archive_sha256": _sha256_file(archive_path),
                    "bundle_archive_format": "tar.gz",
                    "bundle_archive_byte_length": archive_size,
                }
            )
    return {**config, "network_config_hash": _public_network_config_hash_v0(config)}


def attach_public_network_config_quorum_v0(
    *,
    network_config: Mapping[str, Any],
    registry: Mapping[str, Any],
    envelopes: list[Mapping[str, Any]],
) -> dict[str, Any]:
    config = dict(network_config)
    config_hash = str(config.get("network_config_hash", _public_network_config_hash_v0(config)))
    if config_hash != _public_network_config_hash_v0(config):
        raise ValueError("public network config hash mismatch")
    admission = verify_signature_quorum_v0(
        registry=registry,
        payload_kind="public_network_config",
        payload_hash=config_hash,
        envelopes=envelopes,
    )
    return {
        **config,
        "network_config_hash": config_hash,
        "config_signer_registry": dict(registry),
        "config_signature_envelopes": [dict(envelope) for envelope in envelopes],
        "network_config_quorum_admission": admission,
    }


def _public_network_config_quorum_admission_v0(
    *,
    network_config: Mapping[str, Any],
    require_network_config_quorum: bool,
    expected_config_signer_registry_hash: str | None,
) -> dict[str, Any] | None:
    if not require_network_config_quorum:
        return None
    registry = network_config.get("config_signer_registry")
    envelopes = network_config.get("config_signature_envelopes")
    if registry is None or envelopes is None:
        raise ValueError("public network config signature quorum is required")
    if expected_config_signer_registry_hash is None:
        raise ValueError("signer registry hash is required when quorum is required")
    if not isinstance(registry, Mapping):
        raise ValueError("config_signer_registry must be an object")
    if registry.get("registry_hash") != expected_config_signer_registry_hash:
        raise ValueError("config signer registry hash mismatch")
    if not isinstance(envelopes, list):
        raise ValueError("config_signature_envelopes must be a list")
    return verify_signature_quorum_v0(
        registry=registry,
        payload_kind="public_network_config",
        payload_hash=str(network_config["network_config_hash"]),
        envelopes=[dict(envelope) for envelope in envelopes if isinstance(envelope, Mapping)],
    )


def _public_network_config_peer_admission_v0(
    *,
    writer_urls: list[str],
    peer_urls: list[str],
    submit_peer_url: str,
) -> dict[str, Any]:
    admitted_writers = _unique_strings(writer_urls)
    admitted_peers = _unique_strings([*writer_urls, *peer_urls])
    if submit_peer_url not in admitted_writers:
        raise ValueError("submit_peer_url must match an admitted writer URL")
    return {
        "writer_count": len(admitted_writers),
        "peer_count": len(admitted_peers),
        "submit_peer_url": submit_peer_url,
    }


def doctor_public_node_v0(
    *,
    config_url: str,
    expected_network_config_hash: str | None = None,
    require_network_config_quorum: bool = False,
    expected_config_signer_registry_hash: str | None = None,
) -> dict[str, Any]:
    checks: list[dict[str, Any]] = []
    remote_network: dict[str, Any] = {}
    try:
        network_config = _fetch_json_url(config_url)
        if network_config.get("schema") != NODE_PUBLIC_NETWORK_CONFIG_SCHEMA:
            raise ValueError("public network config schema mismatch")
        actual_hash = str(network_config.get("network_config_hash", ""))
        if actual_hash == "" or actual_hash != _public_network_config_hash_v0(network_config):
            raise ValueError("public network config hash mismatch")
        if expected_network_config_hash is not None and actual_hash != expected_network_config_hash:
            raise ValueError("public network config hash did not match expected hash")
        quorum_admission = _public_network_config_quorum_admission_v0(
            network_config=network_config,
            require_network_config_quorum=require_network_config_quorum,
            expected_config_signer_registry_hash=expected_config_signer_registry_hash,
        )
        remote_network = {
            "network_id": network_config.get("network_id"),
            "chain_id": network_config.get("chain_id"),
            "network_config_hash": actual_hash,
            "network_config_quorum_required": require_network_config_quorum,
        }
        if quorum_admission is not None:
            remote_network["network_config_quorum_admission"] = quorum_admission
        checks.append({"name": "public_network_config", "ok": True})
    except Exception as exc:
        checks.append({"name": "public_network_config", "ok": False, "error": str(exc)})
    ok = all(check["ok"] is True for check in checks)
    return {
        "schema": "zenodex.zeno_ledger.public_node_doctor.v0",
        "ok": ok,
        "status": "accepted" if ok else "rejected",
        "config_url": config_url,
        "remote_network": remote_network,
        "checks": checks,
    }


def _public_network_config_to_join_config_v0(
    *,
    network_config: Mapping[str, Any],
    node_id: str,
    bundle_root: Path,
    data_dir: Path,
    host: str,
    port: int | None,
    poll_seconds: int | None,
    serve: bool,
    require_network_config_quorum: bool = False,
    expected_config_signer_registry_hash: str | None = None,
    require_production_key_admission: bool = False,
    production_key_signature_verifier: Any | None = None,
) -> dict[str, Any]:
    if network_config.get("schema") != NODE_PUBLIC_NETWORK_CONFIG_SCHEMA:
        raise ValueError("public network config schema mismatch")
    expected_hash = network_config.get("network_config_hash")
    if expected_hash is not None and expected_hash != _public_network_config_hash_v0(network_config):
        raise ValueError("public network config hash mismatch")
    quorum_admission = _public_network_config_quorum_admission_v0(
        network_config=network_config,
        require_network_config_quorum=require_network_config_quorum,
        expected_config_signer_registry_hash=expected_config_signer_registry_hash,
    )
    if require_production_key_admission:
        validate_public_network_config_update_gate_v0(
            network_config.get("production_key_admission_receipt"),
            packet=network_config.get("production_key_packet"),
            key_descriptors=network_config.get("production_key_descriptors"),
            signature_envelopes=network_config.get("production_key_signature_envelopes"),
            signature_verifier=production_key_signature_verifier,
            expected_target_kind="zeno_ledger_public_network_config",
            expected_target_hash=str(network_config["network_config_hash"]),
            expected_payload_hash=str(network_config["network_config_hash"]),
        )
    writer_urls = _as_string_list(network_config.get("writer_urls"), name="writer_urls")
    peer_urls = _as_string_list(network_config.get("peer_urls"), name="peer_urls")
    if not writer_urls:
        raise ValueError("public network config must contain at least one writer URL")
    recommended = network_config.get("recommended_node")
    if not isinstance(recommended, Mapping):
        recommended = {}
    effective_port = port if port is not None else int(recommended.get("port", 8788))
    effective_poll = poll_seconds if poll_seconds is not None else int(recommended.get("poll_seconds", 5))
    join_config = {
        "schema": NODE_JOIN_CONFIG_SCHEMA,
        "base_url": str(network_config["mirror_base_url"]),
        "bundle_root": str(bundle_root),
        "node_id": node_id,
        "data_dir": str(data_dir),
        "peer_urls": _unique_strings([*writer_urls, *peer_urls]),
        "serve": serve,
        "host": host or str(recommended.get("host", "0.0.0.0")),
        "port": effective_port,
        "poll_seconds": effective_poll,
        "enable_testnet_intake": bool(recommended.get("enable_testnet_intake", True)),
        "enable_testnet_faucet": bool(recommended.get("enable_testnet_faucet", True)),
        "expose_testnet_faucet_http": bool(recommended.get("expose_testnet_faucet_http", False)),
        "submit_peer_url": str(recommended.get("submit_peer_url", writer_urls[0])),
        "min_lp_position_age_seconds": int(recommended.get("min_lp_position_age_seconds", 0)),
        "lp_duration_risk_policy": _lp_duration_risk_policy_name_v0(
            recommended.get("lp_duration_risk_policy", "none")
        ),
    }
    join_config["peer_registry_admission"] = _public_network_config_peer_admission_v0(
        writer_urls=writer_urls,
        peer_urls=peer_urls,
        submit_peer_url=str(join_config["submit_peer_url"]),
    )
    join_config["network_config_quorum_required"] = require_network_config_quorum
    if quorum_admission is not None:
        join_config["network_config_quorum_admission"] = quorum_admission
    join_config["production_key_admission_required"] = require_production_key_admission
    if network_config.get("bundle_archive_format") == "tar.gz":
        archive_url = network_config.get("bundle_archive_url")
        archive_sha = network_config.get("bundle_archive_sha256")
        if isinstance(archive_url, str) and isinstance(archive_sha, str):
            join_config["bundle_archive_url"] = archive_url
            join_config["bundle_archive_sha256"] = archive_sha
            join_config["bundle_archive_format"] = "tar.gz"
    return join_config


def join_public_node_from_network_config_url_v0(
    *,
    config_url: str,
    node_id: str,
    bundle_root: Path,
    data_dir: Path,
    host: str,
    port: int | None,
    poll_seconds: int | None,
    serve: bool,
    write_auth_token_env: str | None = None,
    submit_peer_auth_token_env: str | None = None,
    require_network_config_quorum: bool = False,
    expected_config_signer_registry_hash: str | None = None,
    require_production_key_admission: bool = False,
) -> dict[str, Any]:
    """Join a public ZenoLedger testnet from one published network config URL."""

    network_config = _fetch_json_url(config_url)
    join_config = _public_network_config_to_join_config_v0(
        network_config=network_config,
        node_id=node_id,
        bundle_root=bundle_root,
        data_dir=data_dir,
        host=host,
        port=port,
        poll_seconds=poll_seconds,
        serve=serve,
        require_network_config_quorum=require_network_config_quorum,
        expected_config_signer_registry_hash=expected_config_signer_registry_hash,
        require_production_key_admission=require_production_key_admission,
    )
    if write_auth_token_env:
        join_config["write_auth_token_env"] = write_auth_token_env
    if submit_peer_auth_token_env:
        join_config["submit_peer_auth_token_env"] = submit_peer_auth_token_env
    data_dir.mkdir(parents=True, exist_ok=True)
    network_config_path = data_dir / "public_network_config.json"
    join_config_path = data_dir / "node_join_config.json"
    _write_json(network_config_path, network_config)
    _write_json(join_config_path, join_config)
    report = join_public_node_from_config_v0(config_path=join_config_path)
    report["network_config_url"] = config_url
    report["network_config_path"] = str(network_config_path)
    report["network_config_hash"] = network_config.get("network_config_hash")
    return report


def _cmd_bootstrap(args: argparse.Namespace) -> int:
    try:
        report = build_public_testnet_bundle_v0(
            out_dir=args.out_dir,
            network_id=args.network_id,
            chain_id=args.chain_id,
            sequencer_id=args.sequencer_id,
            time_ms=args.time_ms,
            token_symbol=args.token_symbol,
        )
    except Exception as exc:
        report = {"schema": NODE_REPORT_SCHEMA, "ok": False, "status": "rejected", "errors": [str(exc)]}
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
            "covered_feature_count",
            "covered_features",
        )
        if key in report
    }
    if report.get("ok") is not True:
        errors = report.get("errors")
        public_report["error_count"] = len(errors) if isinstance(errors, list) else 1
    _write_stdout_json(public_report)
    return 0 if report.get("ok") is True else 1


def _cmd_sync(args: argparse.Namespace) -> int:
    try:
        report = sync_public_bundle_from_url_v0(
            base_url=args.base_url,
            out_dir=args.out_dir,
        )
    except Exception as exc:
        report = {"schema": NODE_SYNC_REPORT_SCHEMA, "ok": False, "status": "rejected", "errors": [str(exc)]}
    print(json_dumps_for_log(report, indent=2, sort_keys=True))
    return 0 if report.get("ok") is True else 1


def _cmd_preflight(args: argparse.Namespace) -> int:
    report = preflight_node_join_config_v0(
        config_path=args.config,
        check_port=not args.skip_port_check,
        strict_exposure=args.strict_exposure,
        public_operator=args.public_operator,
    )
    print(json_dumps_for_log(report, indent=2, sort_keys=True))
    return 0 if report.get("ok") is True else 1


def _cmd_write_network_config(args: argparse.Namespace) -> int:
    try:
        report = build_public_network_config_v0(
            bundle_root=args.bundle_root,
            mirror_base_url=args.mirror_base_url,
            writer_urls=list(args.writer_url),
            peer_urls=list(args.peer_url),
            poll_seconds=args.poll_seconds,
            node_port=args.node_port,
            min_lp_position_age_seconds=args.min_lp_position_age_seconds,
            lp_duration_risk_policy=args.lp_duration_risk_policy,
        )
        _write_json(args.out, report)
        report = {**report, "config_path": str(args.out)}
    except Exception as exc:
        report = {"schema": NODE_PUBLIC_NETWORK_CONFIG_SCHEMA, "ok": False, "status": "rejected", "errors": [str(exc)]}
    print(json_dumps_for_log(report, indent=2, sort_keys=True))
    return 0 if "errors" not in report else 1


def _cmd_run(args: argparse.Namespace) -> int:
    try:
        report = run_node_once_v0(
            bundle_root=args.bundle_root,
            node_id=args.node_id,
            data_dir=args.data_dir,
            observed_time_ms=args.observed_time_ms,
            peer_watcher_attestation_paths=list(args.peer_watcher_attestation),
        )
    except Exception as exc:
        report = {"schema": NODE_REPORT_SCHEMA, "ok": False, "status": "rejected", "errors": [str(exc)]}
    print(json_dumps_for_log(report, indent=2, sort_keys=True))
    if report.get("ok") is not True:
        return 1
    if args.serve:
        serve_node_v0(
            data_dir=args.data_dir,
            host=args.host,
            port=args.port,
            peer_urls=list(args.peer_url),
            poll_seconds=args.poll_seconds,
            enable_testnet_intake=args.enable_testnet_intake,
            enable_testnet_faucet=args.enable_testnet_faucet,
            expose_testnet_faucet_http=args.expose_testnet_faucet_http,
            allow_unauthenticated_testnet_writes=args.allow_unauthenticated_testnet_writes,
            submit_peer_url=args.submit_peer_url,
            write_auth_token=_auth_token_from_env_name(args.write_auth_token_env, name="write_auth_token_env"),
            submit_peer_auth_token=_auth_token_from_env_name(args.submit_peer_auth_token_env, name="submit_peer_auth_token_env"),
        )
    return 0


def _cmd_append(args: argparse.Namespace) -> int:
    try:
        tx = _load_json_object(args.tx)
        report = append_dex_transaction_v0(
            data_dir=args.data_dir,
            tx=tx,
            time_ms=args.time_ms,
        )
    except Exception as exc:
        report = {"schema": NODE_APPEND_REPORT_SCHEMA, "ok": False, "status": "rejected", "errors": [str(exc)]}
    print(json_dumps_for_log(report, indent=2, sort_keys=True))
    return 0 if report.get("ok") is True else 1


def _cmd_pull_live(args: argparse.Namespace) -> int:
    try:
        report = pull_live_from_peer_v0(
            data_dir=args.data_dir,
            peer_url=args.peer_url,
        )
    except Exception as exc:
        report = {"schema": NODE_PULL_REPORT_SCHEMA, "ok": False, "status": "rejected", "errors": [str(exc)]}
    print(json_dumps_for_log(report, indent=2, sort_keys=True))
    return 0 if report.get("ok") is True else 1


def _cmd_check_peers(args: argparse.Namespace) -> int:
    try:
        report = check_peer_status_v0(
            data_dir=args.data_dir,
            peer_urls=list(args.peer_url),
        )
    except Exception as exc:
        report = {"schema": NODE_PEER_CHECK_REPORT_SCHEMA, "ok": False, "status": "rejected", "errors": [str(exc)]}
    print(json_dumps_for_log(report, indent=2, sort_keys=True))
    return 0 if report.get("ok") is True else 1


def _cmd_join(args: argparse.Namespace) -> int:
    try:
        report = join_public_node_from_config_v0(config_path=args.config)
    except Exception as exc:
        report = {"schema": NODE_JOIN_REPORT_SCHEMA, "ok": False, "status": "rejected", "errors": [str(exc)]}
    print(json_dumps_for_log(report, indent=2, sort_keys=True))
    if report.get("ok") is not True:
        return 1
    config = dict(_load_json_object(args.config))
    if config.get("serve") is True:
        serve_node_v0(
            data_dir=_as_path(config.get("data_dir"), name="data_dir"),
            host=str(config.get("host", "127.0.0.1")),
            port=int(config.get("port", 8787)),
            peer_urls=_as_string_list(config.get("peer_urls"), name="peer_urls"),
            poll_seconds=int(config.get("poll_seconds", 0)),
            enable_testnet_intake=config.get("enable_testnet_intake") is True,
            enable_testnet_faucet=config.get("enable_testnet_faucet") is True,
            expose_testnet_faucet_http=config.get("expose_testnet_faucet_http") is True,
            allow_unauthenticated_testnet_writes=config.get("allow_unauthenticated_testnet_writes") is True,
            submit_peer_url=str(config["submit_peer_url"]) if config.get("submit_peer_url") else None,
            write_auth_token=_auth_token_from_config(
                config,
                token_key="write_auth_token",
                env_key="write_auth_token_env",
            ),
            submit_peer_auth_token=_auth_token_from_config(
                config,
                token_key="submit_peer_auth_token",
                env_key="submit_peer_auth_token_env",
            ),
        )
    return 0


def _cmd_join_network(args: argparse.Namespace) -> int:
    try:
        report = join_public_node_from_network_config_url_v0(
            config_url=args.config_url,
            node_id=args.node_id,
            bundle_root=args.bundle_root,
            data_dir=args.data_dir,
            host=args.host,
            port=args.port,
            poll_seconds=args.poll_seconds,
            serve=args.serve,
            write_auth_token_env=args.write_auth_token_env,
            submit_peer_auth_token_env=args.submit_peer_auth_token_env,
            require_network_config_quorum=args.require_network_config_quorum,
            expected_config_signer_registry_hash=args.expected_config_signer_registry_hash,
            require_production_key_admission=args.require_production_key_admission,
        )
    except Exception as exc:
        report = {"schema": NODE_JOIN_REPORT_SCHEMA, "ok": False, "status": "rejected", "errors": [str(exc)]}
    print(json_dumps_for_log(report, indent=2, sort_keys=True))
    if report.get("ok") is not True:
        return 1
    if args.serve:
        join_config = dict(_load_json_object(args.data_dir / "node_join_config.json"))
        serve_node_v0(
            data_dir=args.data_dir,
            host=str(join_config.get("host", "0.0.0.0")),
            port=int(join_config.get("port", 8788)),
            peer_urls=_as_string_list(join_config.get("peer_urls"), name="peer_urls"),
            poll_seconds=int(join_config.get("poll_seconds", 5)),
            enable_testnet_intake=join_config.get("enable_testnet_intake") is True,
            enable_testnet_faucet=join_config.get("enable_testnet_faucet") is True,
            expose_testnet_faucet_http=join_config.get("expose_testnet_faucet_http") is True,
            allow_unauthenticated_testnet_writes=join_config.get("allow_unauthenticated_testnet_writes") is True,
            min_lp_position_age_seconds=int(join_config.get("min_lp_position_age_seconds", 0)),
            lp_duration_risk_policy=_lp_duration_risk_policy_from_name_v0(
                join_config.get("lp_duration_risk_policy", "none")
            ),
            submit_peer_url=str(join_config["submit_peer_url"]) if join_config.get("submit_peer_url") else None,
            write_auth_token=_auth_token_from_config(
                join_config,
                token_key="write_auth_token",
                env_key="write_auth_token_env",
            ),
            submit_peer_auth_token=_auth_token_from_config(
                join_config,
                token_key="submit_peer_auth_token",
                env_key="submit_peer_auth_token_env",
            ),
        )
    return 0


def _cmd_faucet(args: argparse.Namespace) -> int:
    try:
        report = append_testnet_faucet_v0(
            data_dir=args.data_dir,
            to_pubkey=args.to_pubkey,
            asset=args.asset,
            amount=args.amount,
            tx_id=args.tx_id,
            time_ms=args.time_ms,
        )
    except Exception as exc:
        report = {"schema": NODE_APPEND_REPORT_SCHEMA, "ok": False, "status": "rejected", "errors": [str(exc)]}
    print(json_dumps_for_log(report, indent=2, sort_keys=True))
    return 0 if report.get("ok") is True else 1


def _cmd_serve(args: argparse.Namespace) -> int:
    load_node_status_v0(args.data_dir)
    serve_node_v0(
        data_dir=args.data_dir,
        host=args.host,
        port=args.port,
        peer_urls=list(args.peer_url),
        poll_seconds=args.poll_seconds,
        enable_testnet_intake=args.enable_testnet_intake,
        enable_testnet_faucet=args.enable_testnet_faucet,
        expose_testnet_faucet_http=args.expose_testnet_faucet_http,
        allow_unauthenticated_testnet_writes=args.allow_unauthenticated_testnet_writes,
        submit_peer_url=args.submit_peer_url,
        write_auth_token=_auth_token_from_env_name(args.write_auth_token_env, name="write_auth_token_env"),
        submit_peer_auth_token=_auth_token_from_env_name(args.submit_peer_auth_token_env, name="submit_peer_auth_token_env"),
    )
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run a ZenoLedger follower/watcher node")
    sub = parser.add_subparsers(dest="command", required=True)

    bootstrap = sub.add_parser("bootstrap", help="build a public-testnet bundle")
    bootstrap.add_argument("--out-dir", required=True, type=Path)
    bootstrap.add_argument("--network-id", default=DEFAULT_CHAIN_ID)
    bootstrap.add_argument("--chain-id", default=DEFAULT_CHAIN_ID)
    bootstrap.add_argument("--sequencer-id", default=DEFAULT_SEQUENCER_ID)
    bootstrap.add_argument("--time-ms", type=int, default=DEFAULT_TIME_MS)
    bootstrap.add_argument("--token-symbol", default="tZDEX")
    bootstrap.set_defaults(func=_cmd_bootstrap)

    sync = sub.add_parser("sync", help="download and verify a public-testnet bundle from an HTTP mirror")
    sync.add_argument("--base-url", required=True)
    sync.add_argument("--out-dir", required=True, type=Path)
    sync.set_defaults(func=_cmd_sync)

    preflight = sub.add_parser("preflight", help="validate a node join config before sync/replay/serve")
    preflight.add_argument("--config", required=True, type=Path)
    preflight.add_argument("--skip-port-check", action="store_true")
    preflight.add_argument(
        "--strict-exposure",
        action="store_true",
        help="reject public binds with testnet faucet or unsigned testnet intake exposure",
    )
    preflight.add_argument(
        "--public-operator",
        action="store_true",
        help="reject inline secrets and public all-interface binds for operator-facing configs",
    )
    preflight.set_defaults(func=_cmd_preflight)

    write_network_config = sub.add_parser(
        "write-network-config",
        help="write a public network config that remote nodes can join from",
    )
    write_network_config.add_argument("--bundle-root", required=True, type=Path)
    write_network_config.add_argument("--mirror-base-url", required=True)
    write_network_config.add_argument("--writer-url", action="append", required=True)
    write_network_config.add_argument("--peer-url", action="append", default=[])
    write_network_config.add_argument("--poll-seconds", type=int, default=5)
    write_network_config.add_argument("--node-port", type=int, default=8788)
    write_network_config.add_argument("--min-lp-position-age-seconds", type=int, default=0)
    write_network_config.add_argument("--lp-duration-risk-policy", choices=["none", "zeno-oracle"], default="none")
    write_network_config.add_argument("--out", required=True, type=Path)
    write_network_config.set_defaults(func=_cmd_write_network_config)

    join = sub.add_parser("join", help="sync, replay, and optionally serve a node from a JSON config")
    join.add_argument("--config", required=True, type=Path)
    join.set_defaults(func=_cmd_join)

    join_network = sub.add_parser("join-network", help="join a public testnet from one network config URL")
    join_network.add_argument("--config-url", required=True)
    join_network.add_argument("--node-id", required=True)
    join_network.add_argument("--bundle-root", required=True, type=Path)
    join_network.add_argument("--data-dir", required=True, type=Path)
    join_network.add_argument("--serve", action="store_true")
    join_network.add_argument("--host", default="0.0.0.0")
    join_network.add_argument("--port", type=int)
    join_network.add_argument("--poll-seconds", type=int)
    join_network.add_argument("--write-auth-token-env")
    join_network.add_argument("--submit-peer-auth-token-env")
    join_network.add_argument("--require-network-config-quorum", action="store_true")
    join_network.add_argument("--expected-config-signer-registry-hash")
    join_network.add_argument("--require-production-key-admission", action="store_true")
    join_network.set_defaults(func=_cmd_join_network)

    run = sub.add_parser("run", help="replay a bundle and optionally serve node status")
    run.add_argument("--bundle-root", required=True, type=Path)
    run.add_argument("--node-id", required=True)
    run.add_argument("--data-dir", required=True, type=Path)
    run.add_argument("--observed-time-ms", type=int)
    run.add_argument("--peer-watcher-attestation", action="append", default=[], type=Path)
    run.add_argument("--serve", action="store_true")
    run.add_argument("--host", default="127.0.0.1")
    run.add_argument("--port", type=int, default=8787)
    run.add_argument("--peer-url", action="append", default=[])
    run.add_argument("--poll-seconds", type=int, default=0)
    run.add_argument("--enable-testnet-intake", action="store_true")
    run.add_argument("--enable-testnet-faucet", action="store_true")
    run.add_argument(
        "--expose-testnet-faucet-http",
        action="store_true",
        help="local fixture demos only: expose POST /faucet after explicit local_fixture_mode acknowledgement",
    )
    run.add_argument(
        "--allow-unauthenticated-testnet-writes",
        action="store_true",
        help="local loopback demos only: allow enabled testnet write endpoints without bearer auth",
    )
    run.add_argument("--submit-peer-url")
    run.add_argument("--write-auth-token-env")
    run.add_argument("--submit-peer-auth-token-env")
    run.set_defaults(func=_cmd_run)

    append = sub.add_parser("append", help="append one testnet DEX transaction to a node-local live ledger")
    append.add_argument("--data-dir", required=True, type=Path)
    append.add_argument("--tx", required=True, type=Path)
    append.add_argument("--time-ms", type=int, default=DEFAULT_TIME_MS + 1_000_000)
    append.set_defaults(func=_cmd_append)

    pull_live = sub.add_parser("pull-live", help="pull and replay live blocks from a peer node")
    pull_live.add_argument("--data-dir", required=True, type=Path)
    pull_live.add_argument("--peer-url", required=True)
    pull_live.set_defaults(func=_cmd_pull_live)

    check_peers = sub.add_parser("check-peers", help="check peer compatibility and common header prefixes")
    check_peers.add_argument("--data-dir", required=True, type=Path)
    check_peers.add_argument("--peer-url", action="append", required=True)
    check_peers.set_defaults(func=_cmd_check_peers)

    faucet = sub.add_parser("faucet", help="append a testnet-only faucet mint to the live ledger")
    faucet.add_argument("--data-dir", required=True, type=Path)
    faucet.add_argument("--to-pubkey", required=True)
    faucet.add_argument("--asset", required=True)
    faucet.add_argument("--amount", required=True, type=int)
    faucet.add_argument("--tx-id", default="node-testnet-faucet-v0")
    faucet.add_argument("--time-ms", type=int, default=DEFAULT_TIME_MS + 1_000_000)
    faucet.set_defaults(func=_cmd_faucet)

    serve = sub.add_parser("serve", help="serve an existing node data directory")
    serve.add_argument("--data-dir", required=True, type=Path)
    serve.add_argument("--host", default="127.0.0.1")
    serve.add_argument("--port", type=int, default=8787)
    serve.add_argument("--peer-url", action="append", default=[])
    serve.add_argument("--poll-seconds", type=int, default=0)
    serve.add_argument("--enable-testnet-intake", action="store_true")
    serve.add_argument("--enable-testnet-faucet", action="store_true")
    serve.add_argument(
        "--expose-testnet-faucet-http",
        action="store_true",
        help="local fixture demos only: expose POST /faucet after explicit local_fixture_mode acknowledgement",
    )
    serve.add_argument(
        "--allow-unauthenticated-testnet-writes",
        action="store_true",
        help="local loopback demos only: allow enabled testnet write endpoints without bearer auth",
    )
    serve.add_argument("--submit-peer-url")
    serve.add_argument("--write-auth-token-env")
    serve.add_argument("--submit-peer-auth-token-env")
    serve.set_defaults(func=_cmd_serve)

    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
