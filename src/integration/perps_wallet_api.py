"""Tau-node-backed perps wallet API.

This module exposes a mounted live surface for stream-8 clearinghouse perps
operations. It intentionally sits beside ``perps_api.py`` because that module
is a demo/development API and does not verify caller authority.
"""

from __future__ import annotations

import http.client
import json
import os
import smtplib
import ssl
import threading
import time
import uuid
from email.message import EmailMessage
from email.utils import make_msgid
from pathlib import Path
from typing import Any, Dict, Mapping, Optional, Tuple, cast
from urllib.parse import parse_qs, urlsplit

from ..core.dex import DexState
from ..core.perps import PerpClearinghouse2pMarketState, PerpClearinghouseNpMarketState, PerpMarketState
from ..state.canonical import canonical_hex_fixed_allow_0x, canonical_json_bytes, domain_sep_bytes, sha256_hex
from .dex_snapshot import snapshot_with_legacy_lp_metadata_defaults, state_from_snapshot
from .live_proof_wrapper import (
    live_zk_proof_required,
    proof_from_request,
    require_live_proof_wrapper,
    verify_live_proof_wrapper,
)
from .perp_engine import PerpEngineConfig, apply_perp_ops
from .perps_wallet_authority import (
    evaluate_perps_wallet_authority_profile_v1,
    evaluate_perps_wallet_device_approval_exercise_v1,
    evaluate_perps_wallet_hardware_custody_v1,
    evaluate_perps_wallet_recovery_exercise_v1,
    evaluate_perps_wallet_rotation_exercise_v1,
    evaluate_perps_wallet_signer_ceremony_v1,
    evaluate_perps_wallet_signer_device_integration_v1,
    evaluate_perps_wallet_signer_execution_exercise_v1,
    evaluate_perps_wallet_signer_prompt_capture_v1,
)
from .perps_wallet_encrypted_sss_backup import (
    build_perps_wallet_encrypted_sss_live_delivery_receipt_v1,
    evaluate_perps_wallet_encrypted_sss_backup_v1,
    perps_wallet_encrypted_sss_backup_hash_v1,
    recipient_root_keys_from_fixture_v1,
)
try:
    from .production_promotion_evidence import evaluate_production_hardware_wallet_evidence_v1
except ModuleNotFoundError:
    def evaluate_production_hardware_wallet_evidence_v1(
        evidence: Mapping[str, Any] | None,
        *,
        wallet_authority_profile_hash: object | None = None,
        expected_device_pubkey: object | None = None,
        **_: object,
    ) -> dict[str, Any]:
        return {
            "schema": "zenodex/production-hardware-wallet-evidence-status/v1",
            "ok": False,
            "production_ready": False,
            "status": "blocked",
            "lane": "hardware_wallet",
            "evidence_hash": None,
            "wallet_authority_profile_hash": wallet_authority_profile_hash,
            "expected_device_pubkey": expected_device_pubkey,
            "gaps": ["production promotion evidence verifier module is unavailable"],
        }
from .tau_net_client import (
    TauNetRpcError,
    TauNetTcpClient,
    TauNetTcpConfig,
    bls_pubkey_hex_from_privkey,
    build_signed_tau_transaction,
    encode_tau_operations_for_wire,
    tau_rpc_invalid_sequence_numbers,
    sign_perp_op_for_engine,
    tau_rpc_response_is_success,
    verify_tau_transaction_payload_signature,
)
from .zeno_oracle_authority import evaluate_oracle_authority_profile_v1
from .zusd_tau_token import derive_zusd_tau_asset_id


MAX_POST_BODY = 65_536
ResponseT = Tuple[int, Dict[str, Any]]
_STREAM_KEY = "22"
_ENGINE_STREAM_KEY = "5"
_U32_MAX = 0xFFFFFFFF
_ACTIONS = {
    "init_market_2p",
    "init_market_np",
    "join_market",
    "deposit_collateral",
    "withdraw_collateral",
    "deposit_insurance",
    "submit_intent",
    "set_position_pair",
    "advance_epoch",
    "publish_clearing_price",
    "run_epoch",
    "settle_epoch",
    "partial_liquidate",
}
_PERPS_PROOF_PROFILE_ID = "perps_stream8_live_wallet_v0"
_PERPS_PROOF_PROFILE_SCHEMA = "zenodex/perps_wallet/proof_profile/v1"
_PERPS_PROOF_INTENT_SCHEMA = "zenodex/perps_wallet/proof_intent_receipt/v1"
_PERPS_PROOF_INTENT_HASH_DOMAIN = "zenodex.perps_wallet.proof_intent_receipt/v1"
_PERPS_ZK_PROOF_ENV_PREFIX = "PERPS_WALLET"
_PERPS_ZK_PROOF_REQUIRED_ENV = "PERPS_WALLET_REQUIRE_ZK_PROOF"
_PERPS_TAU_WRITE_LOCK = threading.Lock()
_ORACLE_AUTHORITY_EXERCISE_SCHEMA = "zenodex/perps_wallet/oracle_authority_exercise/v1"
_ORACLE_AUTHORITY_EXERCISE_HASH_DOMAIN = "zenodex.perps_wallet.oracle_authority_exercise/v1"
_ORACLE_AUTHORITY_ACTIONS = {"run_epoch", "settle_epoch", "partial_liquidate"}


def _env_str(name: str, default: str) -> str:
    raw = os.environ.get(name)
    if raw is None:
        return default
    value = raw.strip()
    return value if value else default


def _env_bool(name: str, default: bool = False) -> bool:
    raw = os.environ.get(name)
    if raw is None or not raw.strip():
        return bool(default)
    return raw.strip().lower() in {"1", "true", "yes", "on"}


def _env_float(name: str, default: float, *, lo: float, hi: float) -> float:
    raw = os.environ.get(name)
    if raw is None or not raw.strip():
        return float(default)
    try:
        value = float(raw.strip())
    except Exception:
        return float(default)
    return min(max(value, lo), hi)


def _env_int(name: str, default: int, *, lo: int, hi: int) -> int:
    raw = os.environ.get(name)
    if raw is None or not raw.strip():
        return int(default)
    try:
        value = int(raw.strip())
    except Exception:
        return int(default)
    return min(max(value, lo), hi)


def _tau_client() -> TauNetTcpClient:
    return TauNetTcpClient(
        TauNetTcpConfig(
            host=_env_str("PERPS_WALLET_TAU_HOST", _env_str("ZUSD_MONETARY_WALLET_TAU_HOST", "127.0.0.1")),
            port=_env_int(
                "PERPS_WALLET_TAU_PORT",
                _env_int("ZUSD_MONETARY_WALLET_TAU_PORT", 65432, lo=1, hi=65535),
                lo=1,
                hi=65535,
            ),
            timeout_s=_env_float(
                "PERPS_WALLET_TAU_TIMEOUT_S",
                _env_float("ZUSD_MONETARY_WALLET_TAU_TIMEOUT_S", 3.0, lo=0.1, hi=60.0),
                lo=0.1,
                hi=60.0,
            ),
        )
    )


def _tau_chain_id() -> str:
    return _env_str("PERPS_WALLET_CHAIN_ID", _env_str("TAU_DEX_CHAIN_ID", "tau-local"))


def _allow_signing() -> bool:
    return _env_bool("PERPS_WALLET_ALLOW_LOCAL_SIGNING", False)


def _return_signed_tau_tx_payloads() -> bool:
    return _env_bool("PERPS_WALLET_RETURN_SIGNED_TAU_TX_PAYLOAD", False)


def _auto_mine() -> bool:
    return _env_bool("PERPS_WALLET_AUTO_MINE", False)


def _default_deadline() -> int:
    delta = _env_int("PERPS_WALLET_DEFAULT_DEADLINE_S", 3600, lo=1, hi=86_400)
    return int(time.time()) + int(delta)


def _wallet_authority_profile_from_env() -> tuple[Mapping[str, Any] | None, str | None]:
    raw = _env_str("PERPS_WALLET_AUTHORITY_PROFILE_JSON", "")
    if raw:
        try:
            obj = json.loads(raw)
        except (json.JSONDecodeError, UnicodeDecodeError) as exc:
            return None, f"perps wallet authority profile JSON invalid: {exc}"
        if not isinstance(obj, Mapping):
            return None, "perps wallet authority profile JSON must be an object"
        return obj, None

    path_raw = _env_str("PERPS_WALLET_AUTHORITY_PROFILE_FILE", "")
    if path_raw:
        try:
            obj = json.loads(Path(path_raw).read_text(encoding="utf-8"))
        except Exception as exc:
            return None, f"perps wallet authority profile file invalid: {exc}"
        if not isinstance(obj, Mapping):
            return None, "perps wallet authority profile file must contain an object"
        return obj, None

    return None, None


def _wallet_recovery_exercise_from_env() -> tuple[Mapping[str, Any] | None, str | None]:
    return _json_profile_from_env(
        json_names=("PERPS_WALLET_RECOVERY_EXERCISE_JSON",),
        file_names=("PERPS_WALLET_RECOVERY_EXERCISE_FILE",),
        label="perps wallet recovery exercise",
    )


def _wallet_rotation_exercise_from_env() -> tuple[Mapping[str, Any] | None, str | None]:
    return _json_profile_from_env(
        json_names=("PERPS_WALLET_ROTATION_EXERCISE_JSON",),
        file_names=("PERPS_WALLET_ROTATION_EXERCISE_FILE",),
        label="perps wallet rotation exercise",
    )


def _wallet_device_approval_exercise_from_env() -> tuple[Mapping[str, Any] | None, str | None]:
    return _json_profile_from_env(
        json_names=("PERPS_WALLET_DEVICE_APPROVAL_EXERCISE_JSON",),
        file_names=("PERPS_WALLET_DEVICE_APPROVAL_EXERCISE_FILE",),
        label="perps wallet device approval exercise",
    )


def _wallet_signer_device_integration_from_env() -> tuple[Mapping[str, Any] | None, str | None]:
    return _json_profile_from_env(
        json_names=("PERPS_WALLET_SIGNER_DEVICE_INTEGRATION_JSON",),
        file_names=("PERPS_WALLET_SIGNER_DEVICE_INTEGRATION_FILE",),
        label="perps wallet signer-device integration",
    )


def _wallet_signer_execution_exercise_from_env() -> tuple[Mapping[str, Any] | None, str | None]:
    return _json_profile_from_env(
        json_names=("PERPS_WALLET_SIGNER_EXECUTION_EXERCISE_JSON",),
        file_names=("PERPS_WALLET_SIGNER_EXECUTION_EXERCISE_FILE",),
        label="perps wallet signer execution exercise",
    )


def _wallet_signer_prompt_capture_from_env() -> tuple[Mapping[str, Any] | None, str | None]:
    return _json_profile_from_env(
        json_names=("PERPS_WALLET_SIGNER_PROMPT_CAPTURE_JSON",),
        file_names=("PERPS_WALLET_SIGNER_PROMPT_CAPTURE_FILE",),
        label="perps wallet signer prompt capture",
    )


def _wallet_encrypted_sss_backup_from_env() -> tuple[Mapping[str, Any] | None, str | None]:
    return _json_profile_from_env(
        json_names=("PERPS_WALLET_ENCRYPTED_SSS_BACKUP_JSON",),
        file_names=("PERPS_WALLET_ENCRYPTED_SSS_BACKUP_FILE",),
        label="perps wallet encrypted SSS backup",
    )


def _wallet_encrypted_sss_recipient_keys_from_env() -> tuple[dict[str, bytes] | None, str | None]:
    raw, err = _json_profile_from_env(
        json_names=("PERPS_WALLET_ENCRYPTED_SSS_RECIPIENT_KEYS_JSON",),
        file_names=("PERPS_WALLET_ENCRYPTED_SSS_RECIPIENT_KEYS_FILE",),
        label="perps wallet encrypted SSS recipient keys",
    )
    if err is not None or raw is None:
        return None, err
    try:
        return recipient_root_keys_from_fixture_v1(raw), None
    except Exception as exc:
        return None, f"perps wallet encrypted SSS recipient keys invalid: {exc}"


def _provider_delivery_mode(envelope: Mapping[str, Any]) -> str:
    provider_kind = str(envelope.get("provider_kind") or "")
    provider_id = str(envelope.get("provider_id") or "")
    if provider_kind == "recovery_email":
        return "smtp"
    if provider_kind == "offline_export":
        return "offline_export"
    if provider_kind == "cloud_drive" and provider_id.startswith("box:"):
        return "box"
    if provider_kind == "cloud_drive":
        return "dropbox"
    raise ValueError(f"unsupported encrypted SSS provider kind: {provider_kind}")


def _required_env(name: str) -> str:
    value = _env_str(name, "")
    if not value:
        raise ValueError(f"missing required env: {name}")
    return value


def _safe_provider_filename_component(raw: object) -> str:
    text = str(raw or "").strip()
    cleaned = "".join(ch if ch.isalnum() or ch in {"-", "_", "."} else "_" for ch in text)
    cleaned = cleaned.strip("._")
    return cleaned[:96] or "encrypted-sss-share"


def _provider_delivery_payload_bytes(envelope: Mapping[str, Any]) -> bytes:
    return canonical_json_bytes(
        {
            "schema": "zenodex/perps-wallet-encrypted-sss-provider-payload/v1",
            "envelope": dict(envelope),
        }
    )


def _provider_delivery_filename(envelope: Mapping[str, Any], *, delivered_at_epoch: int) -> str:
    share = _safe_provider_filename_component(envelope.get("share_id"))
    envelope_hash = str(envelope.get("envelope_hash") or "").removeprefix("0x")[:16]
    nonce = uuid.uuid4().hex[:16]
    return f"{share}-{delivered_at_epoch}-{envelope_hash}-{nonce}.json"


def _email_recipient_from_provider_id(provider_id: str) -> str:
    if not provider_id.startswith("email:"):
        raise ValueError("recovery_email provider_id must start with email:")
    recipient = provider_id.removeprefix("email:").strip()
    if "@" not in recipient or recipient.startswith("@") or recipient.endswith("@"):
        raise ValueError("recovery_email provider_id is not a valid email destination")
    return recipient


def _https_post_json(url: str, *, body: bytes, headers: Mapping[str, str], label: str) -> Mapping[str, Any]:
    parsed = urlsplit(url)
    if parsed.scheme != "https" or not parsed.hostname:
        raise ValueError(f"{label} endpoint must be absolute https")
    path = parsed.path or "/"
    if parsed.query:
        path = f"{path}?{parsed.query}"
    timeout = _env_float("PERPS_WALLET_ENCRYPTED_SSS_HTTP_TIMEOUT_S", 20.0, lo=1.0, hi=120.0)
    conn = http.client.HTTPSConnection(
        parsed.hostname,
        parsed.port or 443,
        timeout=timeout,
        context=ssl.create_default_context(),
    )
    try:
        conn.request("POST", path, body=body, headers=dict(headers))
        response = conn.getresponse()
        response_body = response.read()
    finally:
        conn.close()
    if response.status < 200 or response.status >= 300:
        detail = response_body[:240].decode("utf-8", errors="replace")
        raise ValueError(f"{label} upload failed with HTTP {response.status}: {detail}")
    try:
        payload = json.loads(response_body.decode("utf-8"))
    except (json.JSONDecodeError, UnicodeDecodeError) as exc:
        raise ValueError(f"{label} upload returned non-JSON response: {exc}") from exc
    if not isinstance(payload, Mapping):
        raise ValueError(f"{label} upload returned non-object response")
    return payload


def _multipart_form_data(
    *,
    fields: Mapping[str, tuple[str, bytes, str | None]],
    boundary: str,
) -> bytes:
    chunks: list[bytes] = []
    for name, (filename, value, content_type) in fields.items():
        chunks.append(f"--{boundary}\r\n".encode("ascii"))
        disposition = f'Content-Disposition: form-data; name="{name}"'
        if filename:
            disposition += f'; filename="{filename}"'
        chunks.append(f"{disposition}\r\n".encode("utf-8"))
        if content_type:
            chunks.append(f"Content-Type: {content_type}\r\n".encode("ascii"))
        chunks.append(b"\r\n")
        chunks.append(value)
        chunks.append(b"\r\n")
    chunks.append(f"--{boundary}--\r\n".encode("ascii"))
    return b"".join(chunks)


def _preflight_provider_delivery_config(envelopes: list[Mapping[str, Any]]) -> None:
    modes = {_provider_delivery_mode(envelope) for envelope in envelopes}
    missing: list[str] = []
    if "smtp" in modes:
        for name in ("PERPS_WALLET_ENCRYPTED_SSS_SMTP_HOST", "PERPS_WALLET_ENCRYPTED_SSS_SMTP_FROM"):
            if not _env_str(name, ""):
                missing.append(name)
        username = _env_str("PERPS_WALLET_ENCRYPTED_SSS_SMTP_USERNAME", "")
        password = os.environ.get("PERPS_WALLET_ENCRYPTED_SSS_SMTP_PASSWORD", "")
        if bool(username) != bool(password):
            missing.append("PERPS_WALLET_ENCRYPTED_SSS_SMTP_USERNAME_AND_PASSWORD")
    if "dropbox" in modes and not _env_str("PERPS_WALLET_ENCRYPTED_SSS_DROPBOX_ACCESS_TOKEN", ""):
        missing.append("PERPS_WALLET_ENCRYPTED_SSS_DROPBOX_ACCESS_TOKEN")
    if "box" in modes:
        for name in (
            "PERPS_WALLET_ENCRYPTED_SSS_BOX_ACCESS_TOKEN",
            "PERPS_WALLET_ENCRYPTED_SSS_BOX_PARENT_FOLDER_ID",
        ):
            if not _env_str(name, ""):
                missing.append(name)
    if "offline_export" in modes:
        raw_dir = _env_str("PERPS_WALLET_ENCRYPTED_SSS_OFFLINE_EXPORT_DIR", "")
        if not raw_dir:
            missing.append("PERPS_WALLET_ENCRYPTED_SSS_OFFLINE_EXPORT_DIR")
        else:
            export_dir = Path(raw_dir).expanduser()
            if not export_dir.is_dir():
                missing.append("PERPS_WALLET_ENCRYPTED_SSS_OFFLINE_EXPORT_DIR_EXISTING_DIRECTORY")
    if missing:
        raise ValueError("encrypted_sss_delivery_provider_not_configured:" + ",".join(sorted(missing)))


def _smtp_delivery_fields(
    envelope: Mapping[str, Any],
    *,
    payload: bytes,
    delivered_at_epoch: int,
) -> dict[str, Any]:
    share_id = str(envelope.get("share_id") or "")
    provider_id = str(envelope.get("provider_id") or "")
    recipient = _email_recipient_from_provider_id(provider_id)
    host = _required_env("PERPS_WALLET_ENCRYPTED_SSS_SMTP_HOST")
    sender = _required_env("PERPS_WALLET_ENCRYPTED_SSS_SMTP_FROM")
    port = _env_int("PERPS_WALLET_ENCRYPTED_SSS_SMTP_PORT", 587, lo=1, hi=65535)
    timeout = _env_float("PERPS_WALLET_ENCRYPTED_SSS_SMTP_TIMEOUT_S", 20.0, lo=1.0, hi=120.0)
    starttls = _env_bool("PERPS_WALLET_ENCRYPTED_SSS_SMTP_STARTTLS", True)
    username = _env_str("PERPS_WALLET_ENCRYPTED_SSS_SMTP_USERNAME", "")
    password = os.environ.get("PERPS_WALLET_ENCRYPTED_SSS_SMTP_PASSWORD", "")
    if bool(username) != bool(password):
        raise ValueError("SMTP username and password must be configured together")

    message_id = make_msgid(idstring=_safe_provider_filename_component(share_id))
    message = EmailMessage()
    message["From"] = sender
    message["To"] = recipient
    message["Subject"] = f"ZenoDEX encrypted SSS share {share_id}"
    message["Message-ID"] = message_id
    message.set_content(
        "Encrypted SSS backup share envelope attached. "
        "This message contains encrypted transport material only."
    )
    message.add_attachment(
        payload,
        maintype="application",
        subtype="json",
        filename=_provider_delivery_filename(envelope, delivered_at_epoch=delivered_at_epoch),
    )

    with smtplib.SMTP(host, port, timeout=timeout) as smtp:
        smtp.ehlo()
        if starttls:
            smtp.starttls(context=ssl.create_default_context())
            smtp.ehlo()
        if username and password:
            smtp.login(username, password)
        refused = smtp.send_message(message)
    if refused:
        raise ValueError("SMTP refused encrypted SSS recipient")

    provider_response_hash = sha256_hex(
        canonical_json_bytes(
            {
                "mode": "smtp",
                "provider_id": provider_id,
                "share_id": share_id,
                "envelope_hash": envelope.get("envelope_hash"),
                "delivered_at_epoch": delivered_at_epoch,
                "smtp_message_id": message_id,
                "refused": refused,
            }
        )
    )
    return {
        "provider_response_hash": provider_response_hash,
        "receipt_reference": f"smtp:{message_id}",
        "smtp_message_id": message_id,
    }


def _dropbox_delivery_fields(
    envelope: Mapping[str, Any],
    *,
    payload: bytes,
    delivered_at_epoch: int,
) -> dict[str, Any]:
    token = _required_env("PERPS_WALLET_ENCRYPTED_SSS_DROPBOX_ACCESS_TOKEN")
    folder = _env_str("PERPS_WALLET_ENCRYPTED_SSS_DROPBOX_FOLDER", "/zenodex-encrypted-sss").rstrip("/")
    if not folder.startswith("/"):
        raise ValueError("PERPS_WALLET_ENCRYPTED_SSS_DROPBOX_FOLDER must start with /")
    filename = _provider_delivery_filename(envelope, delivered_at_epoch=delivered_at_epoch)
    dropbox_path = f"{folder}/{filename}"
    api_arg = json.dumps(
        {
            "path": dropbox_path,
            "mode": "add",
            "autorename": True,
            "mute": False,
            "strict_conflict": False,
        },
        separators=(",", ":"),
    )
    response = _https_post_json(
        "https://content.dropboxapi.com/2/files/upload",
        body=payload,
        headers={
            "Authorization": f"Bearer {token}",
            "Content-Type": "application/octet-stream",
            "Dropbox-API-Arg": api_arg,
        },
        label="dropbox encrypted SSS delivery",
    )
    file_id = response.get("id")
    revision = response.get("rev")
    if not isinstance(file_id, str) or not file_id.strip():
        raise ValueError("dropbox encrypted SSS delivery response missing id")
    if not isinstance(revision, str) or not revision.strip():
        raise ValueError("dropbox encrypted SSS delivery response missing rev")
    return {
        "provider_response_hash": sha256_hex(canonical_json_bytes(dict(response))),
        "receipt_reference": f"dropbox:{dropbox_path}",
        "provider_file_id": file_id,
        "provider_revision": revision,
    }


def _box_delivery_fields(
    envelope: Mapping[str, Any],
    *,
    payload: bytes,
    delivered_at_epoch: int,
) -> dict[str, Any]:
    token = _required_env("PERPS_WALLET_ENCRYPTED_SSS_BOX_ACCESS_TOKEN")
    parent_folder_id = _required_env("PERPS_WALLET_ENCRYPTED_SSS_BOX_PARENT_FOLDER_ID")
    filename = _provider_delivery_filename(envelope, delivered_at_epoch=delivered_at_epoch)
    attributes = canonical_json_bytes({"name": filename, "parent": {"id": parent_folder_id}})
    boundary = "zenodex-encrypted-sss-" + uuid.uuid4().hex
    body = _multipart_form_data(
        fields={
            "attributes": ("", attributes, "application/json"),
            "file": (filename, payload, "application/json"),
        },
        boundary=boundary,
    )
    response = _https_post_json(
        "https://upload.box.com/api/2.0/files/content",
        body=body,
        headers={
            "Authorization": f"Bearer {token}",
            "Content-Type": f"multipart/form-data; boundary={boundary}",
        },
        label="box encrypted SSS delivery",
    )
    entries = response.get("entries")
    entry = entries[0] if isinstance(entries, list) and entries else None
    if not isinstance(entry, Mapping):
        raise ValueError("box encrypted SSS delivery response missing entries")
    file_id = entry.get("id")
    revision = entry.get("etag") or entry.get("sha1")
    if not isinstance(file_id, str) or not file_id.strip():
        raise ValueError("box encrypted SSS delivery response missing id")
    if not isinstance(revision, str) or not str(revision).strip():
        raise ValueError("box encrypted SSS delivery response missing revision")
    return {
        "provider_response_hash": sha256_hex(canonical_json_bytes(dict(response))),
        "receipt_reference": f"box:{file_id}",
        "provider_file_id": file_id,
        "provider_revision": str(revision),
    }


def _offline_export_delivery_fields(
    envelope: Mapping[str, Any],
    *,
    payload: bytes,
    delivered_at_epoch: int,
) -> dict[str, Any]:
    share_id = str(envelope.get("share_id") or "")
    export_root = Path(_required_env("PERPS_WALLET_ENCRYPTED_SSS_OFFLINE_EXPORT_DIR")).expanduser().resolve()
    if not export_root.is_dir():
        raise ValueError("PERPS_WALLET_ENCRYPTED_SSS_OFFLINE_EXPORT_DIR must be an existing directory")
    filename = _provider_delivery_filename(envelope, delivered_at_epoch=delivered_at_epoch)
    export_path = (export_root / filename).resolve()
    if export_root != export_path.parent:
        raise ValueError("offline export path escapes configured export directory")
    fd = os.open(export_path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    with os.fdopen(fd, "wb") as fh:
        fh.write(payload)
    manifest = {
        "schema": "zenodex/perps-wallet-encrypted-sss-offline-export-manifest/v1",
        "filename": filename,
        "payload_sha256": sha256_hex(payload),
        "payload_size": len(payload),
        "envelope_hash": envelope.get("envelope_hash"),
        "share_id": share_id,
        "delivered_at_epoch": delivered_at_epoch,
    }
    manifest_hash = sha256_hex(canonical_json_bytes(manifest))
    manifest_path = export_path.with_suffix(export_path.suffix + ".manifest.json")
    manifest_bytes = canonical_json_bytes({**manifest, "manifest_hash": manifest_hash})
    fd = os.open(manifest_path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    with os.fdopen(fd, "wb") as fh:
        fh.write(manifest_bytes)
    provider_response_hash = sha256_hex(
        canonical_json_bytes(
            {
                "mode": "offline_export",
                "manifest_hash": manifest_hash,
                "manifest_filename": manifest_path.name,
            }
        )
    )
    return {
        "provider_response_hash": provider_response_hash,
        "receipt_reference": f"offline-export:{manifest_hash}",
        "offline_export_manifest_hash": manifest_hash,
    }


def _deliver_encrypted_sss_envelope(
    envelope: Mapping[str, Any],
    *,
    mode: str,
    delivered_at_epoch: int,
) -> dict[str, Any]:
    payload = _provider_delivery_payload_bytes(envelope)
    if mode == "smtp":
        return _smtp_delivery_fields(envelope, payload=payload, delivered_at_epoch=delivered_at_epoch)
    if mode == "dropbox":
        return _dropbox_delivery_fields(envelope, payload=payload, delivered_at_epoch=delivered_at_epoch)
    if mode == "box":
        return _box_delivery_fields(envelope, payload=payload, delivered_at_epoch=delivered_at_epoch)
    if mode == "offline_export":
        return _offline_export_delivery_fields(envelope, payload=payload, delivered_at_epoch=delivered_at_epoch)
    raise ValueError(f"unsupported encrypted SSS delivery mode: {mode}")


def _build_encrypted_sss_provider_delivery_response(parsed: Mapping[str, Any]) -> dict[str, Any]:
    chain_id = str(parsed.get("chain_id") or _tau_chain_id())

    backup_raw = parsed.get("backup")
    if not isinstance(backup_raw, Mapping):
        backup_raw, backup_error = _wallet_encrypted_sss_backup_from_env()
        if backup_error is not None:
            return {"ok": False, "error": backup_error, "production_security_claim": False}
    if not isinstance(backup_raw, Mapping):
        return {"ok": False, "error": "encrypted_sss_backup_missing", "production_security_claim": False}

    delivered_at_epoch = parsed.get("delivered_at_epoch")
    if delivered_at_epoch is None:
        delivered_at_epoch = backup_raw.get("created_at_epoch", 0)
    if not isinstance(delivered_at_epoch, int) or isinstance(delivered_at_epoch, bool) or delivered_at_epoch < 0:
        return {"ok": False, "error": "bad_delivered_at_epoch", "production_security_claim": False}

    backup = dict(backup_raw)
    envelopes = backup.get("envelopes")
    if not isinstance(envelopes, list):
        return {"ok": False, "error": "encrypted_sss_envelopes_missing", "production_security_claim": False}
    envelope_items: list[Mapping[str, Any]] = []
    for item in envelopes:
        if not isinstance(item, Mapping):
            return {"ok": False, "error": "encrypted_sss_envelope_must_be_object", "production_security_claim": False}
        envelope_items.append(item)
    _preflight_provider_delivery_config(envelope_items)

    delivery_evidence: list[dict[str, Any]] = []
    delivery_modes: set[str] = set()
    for item in envelope_items:
        mode = _provider_delivery_mode(item)
        delivery_modes.add(mode)
        fields = _deliver_encrypted_sss_envelope(
            item,
            mode=mode,
            delivered_at_epoch=delivered_at_epoch,
        )
        delivery_evidence.append(
            build_perps_wallet_encrypted_sss_live_delivery_receipt_v1(
                item,
                delivery_mode=mode,
                delivered_at_epoch=delivered_at_epoch,
                **fields,
            )
        )

    backup["delivery_evidence"] = delivery_evidence
    backup["backup_hash"] = perps_wallet_encrypted_sss_backup_hash_v1(backup)

    profile, profile_error = _wallet_authority_profile_from_env()
    recipient_root_keys, recipient_root_keys_error = _wallet_encrypted_sss_recipient_keys_from_env()
    status = evaluate_perps_wallet_encrypted_sss_backup_v1(
        profile,
        backup,
        expected_chain_id=chain_id,
        recipient_root_keys=recipient_root_keys,
    )
    if profile_error is not None:
        status["ok"] = False
        status["encrypted_sss_backup_ready"] = False
        status["status"] = "blocked"
        status.setdefault("errors", []).append(profile_error)
    if recipient_root_keys_error is not None:
        status["ok"] = False
        status["encrypted_sss_backup_ready"] = False
        status["status"] = "blocked"
        status.setdefault("errors", []).append(recipient_root_keys_error)

    return {
        "ok": status.get("encrypted_sss_backup_ready") is True,
        "mode": "real_provider_delivery",
        "delivery_modes": sorted(delivery_modes),
        "provider_delivery_claim": "real_external_delivery_receipts",
        "production_security_claim": status.get("production_security_claim") is True,
        "not_claimed": [
            "does_not_claim_production_custody",
            "does_not_claim_external_audit_completion",
            "does_not_return_encrypted_share_material",
        ],
        "backup_hash": backup.get("backup_hash"),
        "delivery_evidence_hashes": [
            item.get("delivery_hash") for item in delivery_evidence if isinstance(item.get("delivery_hash"), str)
        ],
        "backup_redacted": True,
        "encrypted_sss_backup": status,
    }


def _wallet_production_hardware_evidence_from_env() -> tuple[Mapping[str, Any] | None, str | None]:
    return _json_profile_from_env(
        json_names=("PERPS_WALLET_PRODUCTION_HARDWARE_EVIDENCE_JSON",),
        file_names=("PERPS_WALLET_PRODUCTION_HARDWARE_EVIDENCE_FILE",),
        label="perps wallet production hardware evidence",
    )


def _json_profile_from_env(
    *,
    json_names: tuple[str, ...],
    file_names: tuple[str, ...],
    label: str,
) -> tuple[Mapping[str, Any] | None, str | None]:
    for name in json_names:
        raw = _env_str(name, "")
        if not raw:
            continue
        try:
            obj = json.loads(raw)
        except (json.JSONDecodeError, UnicodeDecodeError) as exc:
            return None, f"{label} JSON invalid from {name}: {exc}"
        if not isinstance(obj, Mapping):
            return None, f"{label} JSON from {name} must be an object"
        return obj, None

    for name in file_names:
        path_raw = _env_str(name, "")
        if not path_raw:
            continue
        try:
            obj = json.loads(Path(path_raw).read_text(encoding="utf-8"))
        except Exception as exc:
            return None, f"{label} file invalid from {name}: {exc}"
        if not isinstance(obj, Mapping):
            return None, f"{label} file from {name} must contain an object"
        return obj, None

    return None, None


def _oracle_authority_profile_from_env() -> tuple[Mapping[str, Any] | None, str | None]:
    return _json_profile_from_env(
        json_names=(
            "PERPS_ORACLE_AUTHORITY_PROFILE_JSON",
            "ZENO_ORACLE_AUTHORITY_PROFILE_JSON",
        ),
        file_names=(
            "PERPS_ORACLE_AUTHORITY_PROFILE_FILE",
            "ZENO_ORACLE_AUTHORITY_PROFILE_FILE",
            "ZENO_ORACLE_PRODUCTION_AUTHORITY_PROFILE_FILE",
        ),
        label="oracle production authority profile",
    )


def _bind_oracle_authority_status(
    status: dict[str, Any],
    *,
    profile: Mapping[str, Any] | None,
    profile_error: str | None,
    expected_chain_id: str,
) -> dict[str, Any]:
    if profile_error is not None:
        status["ok"] = False
        status["production_authority"] = False
        status["status"] = "blocked"
        status.setdefault("readiness_gaps", []).append(profile_error)

    if profile is not None and profile.get("chain_id") != expected_chain_id:
        status["ok"] = False
        status["production_authority"] = False
        status["status"] = "blocked"
        status.setdefault("readiness_gaps", []).append("oracle production authority profile chain_id mismatch")
    return status


def _is_local_chain_id(chain_id: str) -> bool:
    value = str(chain_id or "").strip().lower()
    return (
        value in {"tau-local", "local", "localtest"}
        or "localtest" in value
        or value.endswith("-local")
        or value.startswith("tau-test-")
        or value.startswith("test-")
    )


def _require_production_oracle_authority_for_action(action: str, *, chain_id: str | None = None) -> bool:
    if action not in _ORACLE_AUTHORITY_ACTIONS:
        return False
    default = not _is_local_chain_id(chain_id or _tau_chain_id())
    return _env_bool("PERPS_WALLET_REQUIRE_PRODUCTION_ORACLE_AUTHORITY", default)


def _query_first(query: str, key: str) -> str | None:
    """Return the first value for ``key`` in a URL query string, or None.

    Blank values are treated as absent so an empty ``?account=`` behaves like an
    unauthenticated status request rather than a malformed account.
    """
    values = parse_qs(query).get(key)
    if not values:
        return None
    first = values[0].strip()
    return first or None


def _canonical_pubkey(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    return canonical_hex_fixed_allow_0x(value, nbytes=48, name=name)


def _canonical_asset(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    return canonical_hex_fixed_allow_0x(value, nbytes=32, name=name)


def _pubkey_for_rpc(value: str) -> str:
    s = value.strip().lower()
    return s[2:] if s.startswith("0x") else s


def _pubkey_from_privkey(privkey: object) -> str:
    if not isinstance(privkey, (str, int)):
        raise ValueError("privkey must be string or int")
    return "0x" + bls_pubkey_hex_from_privkey(cast(Any, privkey))


def _parse_json_body(body: Optional[bytes]) -> Tuple[Optional[Dict[str, Any]], Optional[str]]:
    if body is None or len(body) == 0:
        return None, "empty_body"
    if len(body) > MAX_POST_BODY:
        return None, "body_too_large"
    try:
        obj = json.loads(body)
    except (json.JSONDecodeError, UnicodeDecodeError):
        return None, "invalid_json"
    if not isinstance(obj, dict):
        return None, "expected_object"
    return obj, None


def _load_app_state(client: TauNetTcpClient) -> Tuple[Dict[str, Any], Optional[str]]:
    raw = client.getappstate(full=True).strip()
    if not raw:
        raise TauNetRpcError("empty getappstate response")
    obj = json.loads(raw)
    if not isinstance(obj, dict):
        raise TauNetRpcError("invalid getappstate response")
    app_state = obj.get("app_state")
    if app_state is None:
        app_state = {}
    if not isinstance(app_state, dict):
        raise TauNetRpcError("invalid app_state payload")
    app_hash = obj.get("app_hash")
    return app_state, str(app_hash) if isinstance(app_hash, str) and app_hash else None


def _app_hash_wait_timeout_s() -> float:
    return _env_float("PERPS_WALLET_APP_HASH_WAIT_S", 2.0, lo=0.0, hi=30.0)


def _wait_for_app_hash_change(
    client: TauNetTcpClient,
    app_hash_before: str | None,
    *,
    timeout_s: float | None = None,
) -> Tuple[Dict[str, Any], Optional[str]]:
    timeout = _app_hash_wait_timeout_s() if timeout_s is None else max(0.0, float(timeout_s))
    deadline = time.monotonic() + timeout
    last_state: Dict[str, Any] = {}
    last_hash: str | None = None
    while True:
        state, observed_hash = _load_app_state(client)
        last_state = state
        last_hash = observed_hash
        if observed_hash is not None and (
            app_hash_before is None or observed_hash != app_hash_before
        ):
            return state, observed_hash
        if time.monotonic() >= deadline:
            return last_state, last_hash
        time.sleep(0.25)


def _dex_state_view(app_state: Mapping[str, Any]) -> Mapping[str, Any]:
    dex_state = app_state.get("dex_state")
    if isinstance(dex_state, Mapping):
        return dex_state
    return app_state


def _state_from_app_state(app_state: Mapping[str, Any]) -> DexState:
    return state_from_snapshot(snapshot_with_legacy_lp_metadata_defaults(_dex_state_view(app_state)))


def _normalized_balance_key(*, pubkey: object, asset_id: object) -> tuple[str, str]:
    if not isinstance(pubkey, str) or not isinstance(asset_id, str):
        raise TauNetRpcError("balance lookup key invalid")
    return (pubkey.strip().lower(), asset_id.strip().lower())


def _balance_index(app_state: Mapping[str, Any]) -> dict[tuple[str, str], int]:
    state_view = _dex_state_view(app_state)
    raw = state_view.get("balances") or []
    if not isinstance(raw, list):
        raise TauNetRpcError("app_state balances must be a list")
    balances: dict[tuple[str, str], int] = {}
    for index, entry in enumerate(raw):
        if not isinstance(entry, Mapping):
            raise TauNetRpcError(f"app_state.balances[{index}] must be an object")
        entry_pubkey = entry.get("pubkey")
        entry_asset = entry.get("asset")
        amount = entry.get("amount")
        if not isinstance(entry_pubkey, str) or not isinstance(entry_asset, str):
            raise TauNetRpcError(f"app_state.balances[{index}] has invalid keys")
        if not isinstance(amount, int) or isinstance(amount, bool) or amount < 0:
            raise TauNetRpcError(f"app_state.balances[{index}] amount invalid")
        balances.setdefault(
            _normalized_balance_key(pubkey=entry_pubkey, asset_id=entry_asset),
            int(amount),
        )
    return balances


def _indexed_balance_for_asset(
    balance_index: Mapping[tuple[str, str], int],
    *,
    pubkey: str,
    asset_id: str,
) -> int:
    return int(
        balance_index.get(_normalized_balance_key(pubkey=pubkey, asset_id=asset_id), 0)
    )


def _balance_for_asset(app_state: Mapping[str, Any], *, pubkey: str, asset_id: str) -> int:
    return _indexed_balance_for_asset(
        _balance_index(app_state),
        pubkey=pubkey,
        asset_id=asset_id,
    )


def _market_quote_asset(app_state: Mapping[str, Any], *, market_id: str) -> str:
    state = _state_from_app_state(app_state)
    if state.perps is None:
        return ""
    try:
        market = state.perps.get_market(market_id)
    except Exception:
        return ""
    if isinstance(market, PerpClearinghouse2pMarketState):
        return str(market.quote_asset)
    if isinstance(market, PerpClearinghouseNpMarketState):
        return str(market.quote_asset)
    return ""


def _safe_native_balance(client: TauNetTcpClient, pubkey: str) -> int | None:
    try:
        return int(client.get_balance(_pubkey_for_rpc(pubkey)))
    except Exception:
        return None


def _last_used_perp_nonce(app_state: Mapping[str, Any], *, signer_pubkey: str) -> int:
    state_view = _dex_state_view(app_state)
    raw = state_view.get("nonces") or []
    if not isinstance(raw, list):
        raise TauNetRpcError("app_state.nonces must be a list")
    key = _canonical_pubkey(signer_pubkey, name="signer_pubkey")
    last_nonce = 0
    for index, entry in enumerate(raw):
        if not isinstance(entry, Mapping):
            raise TauNetRpcError(f"app_state.nonces[{index}] must be an object")
        pubkey = entry.get("pubkey")
        if not isinstance(pubkey, str):
            raise TauNetRpcError(f"app_state.nonces[{index}].pubkey invalid")
        if pubkey.strip().lower() != key:
            continue
        nonce = entry.get("last_nonce", 0)
        if not isinstance(nonce, int) or isinstance(nonce, bool) or nonce < 0:
            raise TauNetRpcError(f"app_state.nonces[{index}].last_nonce invalid")
        last_nonce = int(nonce)
    return last_nonce


def _request_action(body: Mapping[str, Any]) -> str:
    action = str(body.get("action", "")).strip().lower()
    if action not in _ACTIONS:
        raise ValueError("unsupported_action")
    return action


def _request_u32(body: Mapping[str, Any], *, name: str, default: Optional[int] = None) -> int:
    if name not in body:
        if default is None:
            raise ValueError(f"missing_{name}")
        return int(default)
    value = body.get(name)
    if not isinstance(value, int) or isinstance(value, bool) or value < 0 or value > _U32_MAX:
        raise ValueError(f"bad_{name}")
    return int(value)


def _request_int(body: Mapping[str, Any], *, name: str, default: Optional[int] = None) -> int:
    if name not in body:
        if default is None:
            raise ValueError(f"missing_{name}")
        return int(default)
    value = body.get(name)
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"bad_{name}")
    return int(value)


def _request_int_alias(
    body: Mapping[str, Any],
    *,
    names: tuple[str, ...],
    default: Optional[int] = None,
    non_negative: bool = False,
    positive: bool = False,
) -> int:
    for name in names:
        if name in body:
            value = body.get(name)
            if not isinstance(value, int) or isinstance(value, bool):
                raise ValueError(f"bad_{name}")
            result = int(value)
            if positive and result <= 0:
                raise ValueError(f"bad_{name}")
            if non_negative and result < 0:
                raise ValueError(f"bad_{name}")
            return result
    if default is None:
        raise ValueError(f"missing_{names[0]}")
    result = int(default)
    if positive and result <= 0:
        raise ValueError(f"bad_{names[0]}")
    if non_negative and result < 0:
        raise ValueError(f"bad_{names[0]}")
    return result


def _request_positive_int(body: Mapping[str, Any], *, name: str) -> int:
    value = _request_int(body, name=name)
    if value <= 0:
        raise ValueError(f"bad_{name}")
    return int(value)


def _request_tx_fee_limit(body: Mapping[str, Any]) -> int:
    raw = body.get("tx_fee_limit", 0)
    if isinstance(raw, bool):
        raise ValueError("bad_tx_fee_limit")
    if isinstance(raw, int):
        value = raw
    elif isinstance(raw, str):
        text = raw.strip()
        if not text:
            return 0
        if not text.isdigit():
            raise ValueError("bad_tx_fee_limit")
        value = int(text, 10)
    else:
        raise ValueError("bad_tx_fee_limit")
    if value < 0 or value > 10**30:
        raise ValueError("bad_tx_fee_limit")
    return int(value)


def _testnet_faucet_enabled() -> bool:
    return _env_bool("PERPS_WALLET_TESTNET_FAUCET_ENABLED", False)


def _testnet_faucet_max_amount() -> int:
    return _env_int("PERPS_WALLET_TESTNET_FAUCET_MAX_AMOUNT", 100_000, lo=1, hi=10**18)


def _testnet_faucet_authority_pubkey() -> str:
    raw = _env_str(
        "PERPS_WALLET_TESTNET_FAUCET_AUTHORITY_PUBKEY",
        _env_str("TAU_DEX_OPERATOR_PUBKEY", ""),
    )
    if not raw:
        raise ValueError("perps_wallet_testnet_faucet_authority_missing")
    return _canonical_pubkey(raw, name="testnet_faucet_authority_pubkey")


def _fee_limit_posture(*, tx_fee_limit: int, native_balance: int | None) -> dict[str, Any]:
    ok = None if native_balance is None else bool(int(native_balance) >= int(tx_fee_limit))
    warning = None
    if ok is None and tx_fee_limit > 0:
        warning = "native balance unavailable; Tau fee-limit coverage could not be checked"
    elif ok is False:
        warning = "native balance is below requested Tau fee limit"
    return {
        "tx_fee_limit": str(int(tx_fee_limit)),
        "native_balance": native_balance,
        "native_balance_covers_fee_limit": ok,
        "warning": warning,
    }


def _hash_payload(domain: str, payload: Mapping[str, Any]) -> str:
    return sha256_hex(domain_sep_bytes(domain) + canonical_json_bytes(dict(payload)))


def _redacted_tau_tx_payload(payload: Mapping[str, Any] | None) -> Mapping[str, Any] | None:
    if payload is None:
        return None
    if _return_signed_tau_tx_payloads():
        return dict(payload)
    raw_operations = payload.get("operations")
    operation_streams = sorted(str(key) for key in raw_operations.keys()) if isinstance(raw_operations, Mapping) else []
    return {
        "redacted": True,
        "redaction_reason": "signed_tau_tx_payload_response_redaction",
        "payload_hash": _hash_payload("zenodex.perps_wallet.tau_tx_payload/v1", payload),
        "sender_pubkey": payload.get("sender_pubkey"),
        "sequence_number": payload.get("sequence_number"),
        "expiration_time": payload.get("expiration_time"),
        "fee_limit": str(payload.get("fee_limit")),
        "operation_streams": operation_streams,
    }


def _redact_response_authority_material(payload: dict[str, Any]) -> dict[str, Any]:
    report = payload.get("report")
    if isinstance(report, dict) and isinstance(report.get("tau_tx_payload"), Mapping):
        report["tau_tx_payload"] = _redacted_tau_tx_payload(report.get("tau_tx_payload"))
    return payload


def _perps_proof_profile() -> dict[str, Any]:
    return {
        "schema": _PERPS_PROOF_PROFILE_SCHEMA,
        "profile_id": _PERPS_PROOF_PROFILE_ID,
        "claim_scope": "deterministic_stream8_live_wallet_receipt",
        "covered": [
            "stream8_operation_hash_binding",
            "pre_app_hash_binding",
            "tau_envelope_signature_binding",
            "engine_preflight_replay",
            "post_submit_app_hash_binding_when_available",
            "public_state_delta_witness_binding",
            "oracle_authority_quorum_binding_when_exercised",
        ],
        "not_covered": [
            "risc0_zkvm_wrapper",
            "production_oracle_truth",
            "production_finality",
            "hardware_wallet_key_custody",
            "stream11_zusd_zk_wrapper",
        ],
        "non_claims": [
            "does_not_claim_perps_zk_execution",
            "does_not_claim_oracle_truth_or_governance",
            "does_not_claim_production_finality",
            "does_not_claim_wallet_key_custody",
        ],
        "zk_proof_verified": False,
        "artifact_binding_complete": False,
        "zk_wrapper_required_for_production_claim": True,
        "artifact_binding_required_for_production_claim": True,
        "promotion_ready": False,
    }


def _bind_live_zk_wrapper(
    payload: dict[str, Any],
    *,
    body: Mapping[str, Any],
    required: bool,
    enforce_required: bool = True,
    wrapper_key: str = "zk_wrapper",
) -> dict[str, Any]:
    proof_section = payload.get("proof")
    if not isinstance(proof_section, dict):
        if required and enforce_required:
            raise ValueError("zk_proof_required: missing proof section")
        return payload
    receipt = proof_section.get("intent_receipt")
    if not isinstance(receipt, Mapping):
        if required and enforce_required:
            raise ValueError("zk_proof_required: missing proof intent receipt")
        return payload
    zk_wrapper = verify_live_proof_wrapper(
        surface="perps_stream8",
        env_prefix=_PERPS_ZK_PROOF_ENV_PREFIX,
        proof_intent_receipt=receipt,
        proof=proof_from_request(body),
        required=required,
    )
    proof_section[wrapper_key] = zk_wrapper
    if wrapper_key != "zk_wrapper":
        proof_section["zk_wrapper"] = zk_wrapper
    profile = proof_section.get("profile")
    receipt_body = receipt.get("body") if isinstance(receipt, Mapping) else None
    app_hash_after = receipt_body.get("app_hash_after") if isinstance(receipt_body, Mapping) else None
    state_delta_witness_hash = (
        receipt_body.get("state_delta_witness_hash") if isinstance(receipt_body, Mapping) else None
    )
    post_submit_bound = (
        isinstance(app_hash_after, str)
        and bool(app_hash_after.strip())
        and isinstance(state_delta_witness_hash, str)
        and bool(state_delta_witness_hash.strip())
    )
    if isinstance(profile, dict):
        profile["zk_proof_verified"] = bool(zk_wrapper.get("zk_proof_verified"))
        profile["artifact_binding_complete"] = bool(zk_wrapper.get("artifact_binding_complete"))
        profile["promotion_ready"] = (
            post_submit_bound
            and bool(zk_wrapper.get("zk_proof_verified"))
            and bool(zk_wrapper.get("artifact_binding_complete"))
        )
    if required and zk_wrapper.get("zk_proof_verified") is not True:
        proof_section[f"{wrapper_key}_gap"] = zk_wrapper.get("error") or "proof not verified"
    if enforce_required:
        require_live_proof_wrapper(zk_wrapper)
    return payload


def _reject_payload(payload: dict[str, Any], *, status: str, error: str) -> dict[str, Any]:
    proof_section = payload.get("proof")
    if isinstance(proof_section, dict):
        profile = proof_section.get("profile")
        if isinstance(profile, dict):
            profile["promotion_ready"] = False
    return _redact_response_authority_material({
        **payload,
        "ok": False,
        "status": status,
        "error": error,
    })


def _safe_sequence_after_submission(client: Any, tx_sender_pubkey: str) -> int | None:
    try:
        return int(client.get_sequence(_pubkey_for_rpc(tx_sender_pubkey)))
    except Exception:
        return None


def _invalid_sequence_numbers(response: object) -> tuple[int, int] | None:
    return tau_rpc_invalid_sequence_numbers(response)


def _perps_proof_intent_receipt(
    *,
    chain_id: str,
    action: str,
    operation: Mapping[str, Any],
    operations: Mapping[str, Any],
    app_hash_before: str | None,
    app_hash_after: str | None,
    preflight: Mapping[str, Any],
    tx_sender_pubkey: str,
    tx_sequence_number: int,
    tx_fee_limit: int,
    signing_mode: str,
    tau_tx_payload: Mapping[str, Any] | None,
    state_delta_witness: Mapping[str, Any] | None = None,
    oracle_authority_exercise: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    tau_tx_hash = None
    if tau_tx_payload is not None:
        tau_tx_hash = _hash_payload("zenodex.perps_wallet.tau_tx_payload/v1", tau_tx_payload)
    oracle_authority_exercise_hash = None
    oracle_authority_exercised = False
    if oracle_authority_exercise is not None:
        oracle_authority_exercise_hash = str(oracle_authority_exercise.get("exercise_hash") or "")
        oracle_authority_exercised = bool(oracle_authority_exercise.get("authority_exercised"))
    body: dict[str, Any] = {
        "schema": _PERPS_PROOF_INTENT_SCHEMA,
        "profile_id": _PERPS_PROOF_PROFILE_ID,
        "chain_id": str(chain_id),
        "stream_key": _STREAM_KEY,
        "engine_stream_key": _ENGINE_STREAM_KEY,
        "action": str(action),
        "market_id": operation.get("market_id"),
        "app_hash_before": app_hash_before,
        "app_hash_after": app_hash_after,
        "operation_hash": _hash_payload("zenodex.perps_wallet.operation/v1", operation),
        "operations_hash": _hash_payload("zenodex.perps_wallet.operations/v1", operations),
        "preflight_ok": bool(preflight.get("ok")),
        "preflight_error": preflight.get("error"),
        "tx_sender_pubkey": tx_sender_pubkey,
        "tx_sequence_number": int(tx_sequence_number),
        "tx_fee_limit": str(int(tx_fee_limit)),
        "signing_mode": str(signing_mode),
        "tau_tx_payload_hash": tau_tx_hash,
        "oracle_authority_exercised": oracle_authority_exercised,
        "oracle_authority_exercise_hash": oracle_authority_exercise_hash or None,
        "state_delta_witness_hash": (
            None
            if state_delta_witness is None
            else _hash_payload("zenodex.perps_wallet.state_delta_witness/v1", state_delta_witness)
        ),
        "zk_proof_verified": False,
        "proof_verifier": None,
    }
    return {
        "schema": _PERPS_PROOF_INTENT_SCHEMA,
        "profile_id": _PERPS_PROOF_PROFILE_ID,
        "body": body,
        "oracle_authority_exercise": None if oracle_authority_exercise is None else dict(oracle_authority_exercise),
        "state_delta_witness": None if state_delta_witness is None else dict(state_delta_witness),
        "receipt_hash": _hash_payload(_PERPS_PROOF_INTENT_HASH_DOMAIN, body),
    }


def _oracle_authority_exercise_for_action(
    *,
    action: str,
    chain_id: str,
    operation: Mapping[str, Any],
) -> dict[str, Any] | None:
    if action not in _ORACLE_AUTHORITY_ACTIONS:
        return None

    oracle_authority_profile, oracle_authority_error = _oracle_authority_profile_from_env()
    oracle_authority = _bind_oracle_authority_status(
        evaluate_oracle_authority_profile_v1(oracle_authority_profile),
        profile=oracle_authority_profile,
        profile_error=oracle_authority_error,
        expected_chain_id=chain_id,
    )
    bridge = operation.get("oracle_adapter_bridge")
    bridge_present = isinstance(bridge, Mapping)
    readiness_gaps = list(oracle_authority.get("readiness_gaps") or [])
    if not bridge_present:
        readiness_gaps.append("oracle adapter bridge is missing from operation")

    signature_quorum = oracle_authority.get("signature_quorum")
    if not isinstance(signature_quorum, Mapping):
        signature_quorum = {}
    authority_ready = bool(oracle_authority.get("production_authority"))
    authority_exercised = bool(authority_ready and bridge_present)
    body: dict[str, Any] = {
        "schema": _ORACLE_AUTHORITY_EXERCISE_SCHEMA,
        "action": action,
        "chain_id": chain_id,
        "market_id": operation.get("market_id"),
        "required_for_action": _require_production_oracle_authority_for_action(action, chain_id=chain_id),
        "authority_exercised": authority_exercised,
        "production_authority": authority_ready,
        "status": "exercised" if authority_exercised else "blocked",
        "readiness_gaps": readiness_gaps,
        "authority_id": oracle_authority.get("authority_id"),
        "authority_hash": oracle_authority.get("authority_hash"),
        "expected_authority_hash": oracle_authority.get("expected_authority_hash"),
        "signer_registry_hash": oracle_authority.get("signer_registry_hash"),
        "key_manager_hash": oracle_authority.get("key_manager_hash"),
        "active_signer_count": int(oracle_authority.get("active_signer_count") or 0),
        "threshold": int(oracle_authority.get("threshold") or 0),
        "signature_count": int(oracle_authority.get("signature_count") or 0),
        "signature_quorum_report_hash": signature_quorum.get("quorum_report_hash"),
        "signature_quorum_accepted_weight": int(signature_quorum.get("accepted_weight") or 0),
        "signature_quorum_threshold": int(signature_quorum.get("threshold") or 0),
        "oracle_adapter_bridge_present": bridge_present,
        "oracle_adapter_bridge_id": bridge.get("bridge_id") if isinstance(bridge, Mapping) else None,
        "oracle_adapter_bridge_hash": (
            _hash_payload("zenodex.perps_wallet.oracle_adapter_bridge/v1", bridge)
            if isinstance(bridge, Mapping)
            else None
        ),
    }
    return {
        **body,
        "exercise_hash": _hash_payload(_ORACLE_AUTHORITY_EXERCISE_HASH_DOMAIN, body),
    }


def _perps_state_delta_witness(
    *,
    chain_id: str,
    action: str,
    operation: Mapping[str, Any] | None = None,
    app_hash_before: str | None,
    app_hash_after: str | None,
    app_state_before: Mapping[str, Any],
    app_state_after: Mapping[str, Any],
) -> dict[str, Any]:
    before_markets = _market_summaries(app_state_before)
    after_markets = _market_summaries(app_state_after)
    before_by_id = {str(item.get("market_id")): item for item in before_markets}
    after_by_id = {str(item.get("market_id")): item for item in after_markets}
    changed_markets: list[dict[str, Any]] = []
    numeric_fields = (
        "account_a_quote_balance",
        "account_b_quote_balance",
        "collateral_e8_a",
        "collateral_e8_b",
        "account_count",
        "active_count",
        "claims_paid_e8",
        "clearing_price_seen",
        "fee_pool_e8",
        "funding_rate_bps",
        "insurance_e8",
        "insurance_ext_e8",
        "long_count",
        "net_deposited_e8",
        "pending_intent_count",
        "position_base_a",
        "position_base_b",
        "net_position_base",
        "short_count",
        "index_price_e8",
        "clearing_price_epoch",
        "clearing_price_e8",
        "now_epoch",
        "oracle_last_update_epoch",
        "fee_pool_quote",
        "insurance_balance",
    )
    for market_id in sorted(set(before_by_id) | set(after_by_id)):
        before = before_by_id.get(market_id, {})
        after = after_by_id.get(market_id, {})
        deltas: dict[str, int] = {}
        for field in numeric_fields:
            before_value = before.get(field, 0)
            after_value = after.get(field, 0)
            if isinstance(before_value, int) and isinstance(after_value, int):
                delta = int(after_value) - int(before_value)
                if delta:
                    deltas[field] = delta
        account_deltas: list[dict[str, Any]] = []
        before_accounts_raw = before.get("accounts")
        if isinstance(before_accounts_raw, list):
            before_accounts = {
                str(account.get("account_pubkey")): account
                for account in before_accounts_raw
                if isinstance(account, Mapping)
            }
        else:
            before_accounts = {}
        after_accounts_raw = after.get("accounts")
        if isinstance(after_accounts_raw, list):
            after_accounts = {
                str(account.get("account_pubkey")): account
                for account in after_accounts_raw
                if isinstance(account, Mapping)
            }
        else:
            after_accounts = {}
        for account_pubkey in sorted(set(before_accounts) | set(after_accounts)):
            before_account = before_accounts.get(account_pubkey, {})
            after_account = after_accounts.get(account_pubkey, {})
            account_delta: dict[str, Any] = {"account_pubkey": account_pubkey}
            for field in ("position_base", "collateral_quote", "collateral_e8", "entry_price_e8", "funding_paid_cum_e8", "nonce"):
                before_value = before_account.get(field, 0)
                after_value = after_account.get(field, 0)
                if isinstance(before_value, int) and isinstance(after_value, int):
                    delta = int(after_value) - int(before_value)
                    if delta:
                        account_delta[f"{field}_delta"] = delta
            liquidation_changed = before_account.get("liquidated_this_step") != after_account.get("liquidated_this_step")
            if len(account_delta) > 1 or liquidation_changed:
                account_delta["liquidated_before"] = bool(before_account.get("liquidated_this_step", False))
                account_delta["liquidated_after"] = bool(after_account.get("liquidated_this_step", False))
                account_deltas.append(account_delta)
        market_liquidation_changed = before.get("liquidated_this_step") != after.get("liquidated_this_step")
        if deltas or account_deltas or not before or not after or market_liquidation_changed:
            changed_markets.append(
                {
                    "market_id": market_id,
                    "kind_before": before.get("kind"),
                    "kind_after": after.get("kind"),
                    "deltas": deltas,
                    "account_deltas": account_deltas,
                    "liquidated_before": bool(before.get("liquidated_this_step", False)),
                    "liquidated_after": bool(after.get("liquidated_this_step", False)),
                }
            )
    target_already_satisfied: dict[str, Any] | None = None
    if (
        action == "set_position_pair"
        and isinstance(operation, Mapping)
        and isinstance(operation.get("market_id"), str)
        and isinstance(operation.get("new_position_base_a"), int)
        and isinstance(operation.get("new_position_base_b"), int)
    ):
        target_market_id = str(operation["market_id"])
        before_target = before_by_id.get(target_market_id)
        after_target = after_by_id.get(target_market_id)
        if isinstance(before_target, Mapping) and isinstance(after_target, Mapping):
            new_position_base_a = int(operation["new_position_base_a"])
            new_position_base_b = int(operation["new_position_base_b"])
            before_a = before_target.get("position_base_a")
            before_b = before_target.get("position_base_b")
            after_a = after_target.get("position_base_a")
            after_b = after_target.get("position_base_b")
            satisfied = (
                isinstance(before_a, int)
                and isinstance(before_b, int)
                and isinstance(after_a, int)
                and isinstance(after_b, int)
                and int(before_a) == new_position_base_a
                and int(before_b) == new_position_base_b
                and int(after_a) == new_position_base_a
                and int(after_b) == new_position_base_b
            )
            target_already_satisfied = {
                "kind": "set_position_pair_target_already_satisfied",
                "market_id": target_market_id,
                "new_position_base_a": new_position_base_a,
                "new_position_base_b": new_position_base_b,
                "position_base_a_before": int(before_a) if isinstance(before_a, int) else None,
                "position_base_b_before": int(before_b) if isinstance(before_b, int) else None,
                "position_base_a_after": int(after_a) if isinstance(after_a, int) else None,
                "position_base_b_after": int(after_b) if isinstance(after_b, int) else None,
                "satisfied": bool(satisfied),
            }
    return {
        "schema": "zenodex/perps_wallet/state_delta_witness/v1",
        "chain_id": str(chain_id),
        "stream_key": _STREAM_KEY,
        "action": str(action),
        "app_hash_before": app_hash_before,
        "app_hash_after": app_hash_after,
        "market_count_before": len(before_markets),
        "market_count_after": len(after_markets),
        "changed_markets": changed_markets,
        "target_already_satisfied": target_already_satisfied,
    }


def _state_delta_witness_matches_operation(
    witness: Mapping[str, Any],
    operation: Mapping[str, Any],
) -> bool:
    app_hash_before = witness.get("app_hash_before")
    app_hash_after = witness.get("app_hash_after")
    if not isinstance(app_hash_before, str) or not app_hash_before:
        return False
    if not isinstance(app_hash_after, str) or not app_hash_after:
        return False
    if app_hash_after == app_hash_before:
        return False
    changed_markets = witness.get("changed_markets")
    if not isinstance(changed_markets, list):
        return False
    market_id = operation.get("market_id")
    if not changed_markets:
        target_already_satisfied = witness.get("target_already_satisfied")
        return (
            isinstance(target_already_satisfied, Mapping)
            and target_already_satisfied.get("kind") == "set_position_pair_target_already_satisfied"
            and target_already_satisfied.get("satisfied") is True
            and isinstance(market_id, str)
            and bool(market_id)
            and target_already_satisfied.get("market_id") == market_id
        )
    if isinstance(market_id, str) and market_id:
        for changed_market in changed_markets:
            if isinstance(changed_market, Mapping) and changed_market.get("market_id") == market_id:
                return True
        return False
    return True


def _request_mapping(body: Mapping[str, Any], *, name: str) -> Mapping[str, Any] | None:
    if name not in body:
        return None
    raw = body.get(name)
    if isinstance(raw, str):
        try:
            parsed = json.loads(raw)
        except (json.JSONDecodeError, UnicodeDecodeError) as exc:
            raise ValueError(f"bad_{name}") from exc
        raw = parsed
    if not isinstance(raw, Mapping):
        raise ValueError(f"bad_{name}")
    return raw


def _request_signed_tau_tx_payload(body: Mapping[str, Any]) -> Mapping[str, Any] | None:
    for name in ("signed_tau_tx_payload", "tau_tx_payload"):
        value = _request_mapping(body, name=name)
        if value is not None:
            return value
    return None


def _validate_external_tau_tx_payload(
    payload: Mapping[str, Any],
    *,
    tx_sender_pubkey: str,
    tx_sequence_number: int,
    deadline: int,
    operations: Mapping[str, Any],
    tx_fee_limit: int,
) -> dict[str, Any]:
    sender_raw = payload.get("sender_pubkey")
    if not isinstance(sender_raw, str) or not sender_raw.strip():
        raise ValueError("signed_tau_tx_payload missing sender_pubkey")
    sender_prefixed = sender_raw if sender_raw.lower().startswith("0x") else "0x" + sender_raw
    sender_pubkey = _canonical_pubkey(sender_prefixed, name="signed_tau_tx_payload.sender_pubkey")
    if sender_pubkey.lower() != tx_sender_pubkey.lower():
        raise ValueError("signed_tau_tx_payload sender mismatch")

    sequence_number = payload.get("sequence_number")
    if not isinstance(sequence_number, int) or isinstance(sequence_number, bool):
        raise ValueError("signed_tau_tx_payload bad sequence_number")
    if int(sequence_number) != int(tx_sequence_number):
        raise ValueError("signed_tau_tx_payload sequence mismatch")

    expiration_time = payload.get("expiration_time")
    if not isinstance(expiration_time, int) or isinstance(expiration_time, bool):
        raise ValueError("signed_tau_tx_payload bad expiration_time")
    if int(expiration_time) != int(deadline):
        raise ValueError("signed_tau_tx_payload expiration mismatch")

    if str(payload.get("fee_limit")) != str(tx_fee_limit):
        raise ValueError("signed_tau_tx_payload fee_limit mismatch")

    raw_operations = payload.get("operations")
    if not isinstance(raw_operations, Mapping):
        raise ValueError("signed_tau_tx_payload operations must be an object")
    if dict(raw_operations) != encode_tau_operations_for_wire(operations):
        raise ValueError("signed_tau_tx_payload operations mismatch")

    signature = payload.get("signature")
    if not isinstance(signature, str) or not signature.strip():
        raise ValueError("signed_tau_tx_payload missing signature")
    if not verify_tau_transaction_payload_signature(payload):
        raise ValueError("signed_tau_tx_payload signature invalid")
    return dict(payload)


def _market_id(body: Mapping[str, Any], *, action: str | None = None) -> str:
    raw = str(body.get("market_id") or body.get("marketId") or "").strip()
    if not raw:
        raise ValueError("missing_market_id")
    if len(raw) > 128:
        raise ValueError("bad_market_id")
    if action in {"init_market_np", "join_market", "submit_intent", "run_epoch"}:
        if not raw.startswith("perp:chnp:"):
            raise ValueError("clearinghouse_np market_id must start with perp:chnp:")
        return raw
    if action in {"partial_liquidate", "deposit_insurance"}:
        if not raw.startswith("perp:") or raw.startswith("perp:ch2p:") or raw.startswith("perp:chnp:"):
            raise ValueError("isolated market_id must start with perp: and not clearinghouse prefix")
        return raw
    if action in {"deposit_collateral", "withdraw_collateral", "advance_epoch", "publish_clearing_price", "settle_epoch"}:
        if raw.startswith("perp:ch2p:") or raw.startswith("perp:chnp:"):
            return raw
        raise ValueError("market_id must start with perp:ch2p: or perp:chnp:")
    if action in {"init_market_2p", "set_position_pair"}:
        if not raw.startswith("perp:ch2p:"):
            raise ValueError("market_id must start with perp:ch2p:")
        return raw
    if not raw.startswith("perp:ch2p:"):
        raise ValueError("market_id must start with perp:ch2p:")
    return raw


def _quote_asset(body: Mapping[str, Any], *, chain_id: str) -> str:
    raw = body.get("quote_asset") if "quote_asset" in body else body.get("quoteAsset")
    if isinstance(raw, str) and raw.strip():
        return _canonical_asset(raw, name="quote_asset")
    return derive_zusd_tau_asset_id(chain_id=chain_id)


def _account_pubkey(body: Mapping[str, Any], *, field: str, privkey_field: str) -> str:
    raw = body.get(field)
    if isinstance(raw, str) and raw.strip():
        return _canonical_pubkey(raw, name=field)
    privkey = body.get(privkey_field)
    if privkey is not None:
        return _canonical_pubkey(_pubkey_from_privkey(privkey), name=field)
    raise ValueError(f"missing_{field}")


def _nonce_for_signer(body: Mapping[str, Any], *, app_state: Mapping[str, Any], field: str, signer_pubkey: str) -> int:
    if field in body:
        return _request_u32(body, name=field)
    return _last_used_perp_nonce(app_state, signer_pubkey=signer_pubkey) + 1


def _np_market_now_epoch(app_state: Mapping[str, Any], *, market_id: str) -> int:
    state = _state_from_app_state(app_state)
    if state.perps is None:
        return 0
    try:
        market = state.perps.get_market(market_id)
    except Exception:
        return 0
    if not isinstance(market, PerpClearinghouseNpMarketState):
        return 0
    return int(market.global_state.get("now_epoch", 0))


def _optional_request_mapping(body: Mapping[str, Any], *, name: str) -> Mapping[str, Any] | None:
    raw = body.get(name)
    if raw is None:
        return None
    if isinstance(raw, str):
        text = raw.strip()
        if not text:
            return None
        try:
            raw = json.loads(text)
        except (json.JSONDecodeError, UnicodeDecodeError) as exc:
            raise ValueError(f"bad_{name}") from exc
    if not isinstance(raw, Mapping):
        raise ValueError(f"bad_{name}")
    return raw


def _sign_or_copy(
    body: Mapping[str, Any],
    *,
    op: Mapping[str, Any],
    sig_field: str,
    privkey_field: str,
    chain_id: str,
    signer_pubkey: str,
    nonce: int,
) -> str:
    raw_sig = body.get(sig_field)
    if isinstance(raw_sig, str) and raw_sig.strip():
        return raw_sig.strip()
    privkey = body.get(privkey_field)
    if privkey is None:
        raise ValueError(f"missing_{sig_field}")
    if not _allow_signing():
        raise ValueError("local_signing_disabled")
    return sign_perp_op_for_engine(
        op,
        privkey=cast(Any, privkey),
        chain_id=chain_id,
        signer_pubkey=signer_pubkey,
        nonce=nonce,
    )


def _tx_sender_for_action(body: Mapping[str, Any], *, action: str, account_a_pubkey: str | None, account_pubkey: str | None) -> str:
    raw = body.get("sender_pubkey") if "sender_pubkey" in body else body.get("senderPubkey")
    if isinstance(raw, str) and raw.strip():
        return _canonical_pubkey(raw, name="sender_pubkey")
    if action in {
        "join_market",
        "deposit_collateral",
        "withdraw_collateral",
        "deposit_insurance",
        "submit_intent",
        "publish_clearing_price",
        "partial_liquidate",
    } and account_pubkey is not None:
        return account_pubkey
    if account_a_pubkey is not None:
        return account_a_pubkey
    operator_pubkey = body.get("operator_pubkey") if "operator_pubkey" in body else body.get("operatorPubkey")
    if isinstance(operator_pubkey, str) and operator_pubkey.strip():
        return _canonical_pubkey(operator_pubkey, name="operator_pubkey")
    env_operator = os.environ.get("TAU_DEX_OPERATOR_PUBKEY") or os.environ.get("TAU_DEX_PERP_OPERATOR_PUBKEY")
    if isinstance(env_operator, str) and env_operator.strip():
        return _canonical_pubkey(env_operator, name="operator_pubkey")
    raise ValueError("missing_sender_pubkey")


def _build_operation_and_sender(
    body: Mapping[str, Any],
    *,
    action: str,
    app_state: Mapping[str, Any],
    chain_id: str,
    deadline: int,
) -> tuple[dict[str, Any], str, dict[str, int | str]]:
    market_id = _market_id(body, action=action)
    is_chnp_market = market_id.startswith("perp:chnp:")
    meta: dict[str, int | str] = {}

    if action == "init_market_np":
        params = _optional_request_mapping(body, name="params")
        operation = {
            "module": "TauPerp",
            "version": "1.2",
            "market_id": market_id,
            "action": action,
            "quote_asset": _quote_asset(body, chain_id=chain_id),
            "index_price_e8": _request_int_alias(
                body,
                names=("index_price_e8", "indexPriceE8", "price_e8", "priceE8"),
                positive=True,
            ),
        }
        insurance_seed_e8 = _request_int_alias(
            body,
            names=("insurance_seed_e8", "insuranceSeedE8"),
            default=0,
            non_negative=True,
        )
        if insurance_seed_e8:
            operation["insurance_seed_e8"] = insurance_seed_e8
        if params is not None:
            operation["params"] = dict(params)
        tx_sender = _tx_sender_for_action(body, action=action, account_a_pubkey=None, account_pubkey=None)
        return operation, tx_sender, meta

    if action == "join_market":
        account_pubkey = _account_pubkey(body, field="account_pubkey", privkey_field="account_privkey")
        tx_sender = _tx_sender_for_action(body, action=action, account_a_pubkey=None, account_pubkey=account_pubkey)
        operation = {
            "module": "TauPerp",
            "version": "1.2",
            "market_id": market_id,
            "action": action,
            "account_pubkey": account_pubkey,
        }
        meta.update({"account_pubkey": account_pubkey})
        return operation, tx_sender, meta

    if action in {"deposit_collateral", "withdraw_collateral"}:
        account_pubkey = _account_pubkey(body, field="account_pubkey", privkey_field="account_privkey")
        tx_sender = _tx_sender_for_action(body, action=action, account_a_pubkey=None, account_pubkey=account_pubkey)
        operation = {
            "module": "TauPerp",
            "version": "1.2" if is_chnp_market else "1.0",
            "market_id": market_id,
            "action": action,
            "account_pubkey": account_pubkey,
            "amount": _request_positive_int(body, name="amount"),
        }
        meta.update({"account_pubkey": account_pubkey})
        return operation, tx_sender, meta

    if action == "deposit_insurance":
        account_pubkey = _account_pubkey(body, field="account_pubkey", privkey_field="account_privkey")
        tx_sender = _tx_sender_for_action(body, action=action, account_a_pubkey=None, account_pubkey=account_pubkey)
        operation = {
            "module": "TauPerp",
            "version": "0.1",
            "market_id": market_id,
            "action": action,
            "account_pubkey": account_pubkey,
            "amount": _request_positive_int(body, name="amount"),
        }
        return operation, tx_sender, meta

    if action == "advance_epoch":
        operation = {
            "module": "TauPerp",
            "version": "1.2" if is_chnp_market else "1.0",
            "market_id": market_id,
            "action": action,
        }
        if not is_chnp_market:
            operation["delta"] = _request_u32(body, name="delta", default=1)
        tx_sender = _tx_sender_for_action(body, action=action, account_a_pubkey=None, account_pubkey=None)
        return operation, tx_sender, meta

    if action in {"run_epoch", "settle_epoch"}:
        operation = {
            "module": "TauPerp",
            "version": "1.2" if is_chnp_market else "1.0",
            "market_id": market_id,
            "action": action,
        }
        if is_chnp_market:
            operation["funding_rate_bps"] = _request_int(body, name="funding_rate_bps", default=0)
        bridge = _request_mapping(body, name="oracle_adapter_bridge")
        if bridge is not None:
            operation["oracle_adapter_bridge"] = dict(bridge)
        tx_sender = _tx_sender_for_action(body, action=action, account_a_pubkey=None, account_pubkey=None)
        return operation, tx_sender, meta

    if action == "partial_liquidate":
        account_pubkey = _account_pubkey(body, field="account_pubkey", privkey_field="account_privkey")
        fraction_bps = _request_u32(body, name="fraction_bps")
        if fraction_bps > 10_000:
            raise ValueError("bad_fraction_bps")
        operation = {
            "module": "TauPerp",
            "version": "0.1",
            "market_id": market_id,
            "action": action,
            "account_pubkey": account_pubkey,
            "fraction_bps": fraction_bps,
        }
        bridge = _request_mapping(body, name="oracle_adapter_bridge")
        if bridge is not None:
            operation["oracle_adapter_bridge"] = dict(bridge)
        tx_sender = _tx_sender_for_action(body, action=action, account_a_pubkey=None, account_pubkey=account_pubkey)
        meta.update({"account_pubkey": account_pubkey})
        return operation, tx_sender, meta

    if action == "publish_clearing_price":
        oracle_pubkey_raw = body.get("oracle_pubkey") if "oracle_pubkey" in body else body.get("oraclePubkey")
        if isinstance(oracle_pubkey_raw, str) and oracle_pubkey_raw.strip():
            oracle_pubkey = _canonical_pubkey(oracle_pubkey_raw, name="oracle_pubkey")
        elif body.get("oracle_privkey") is not None:
            oracle_pubkey = _canonical_pubkey(_pubkey_from_privkey(body.get("oracle_privkey")), name="oracle_pubkey")
        else:
            env_oracle = os.environ.get("TAU_DEX_PERP_ORACLE_PUBKEY") or os.environ.get("TAU_DEX_ORACLE_PUBKEY")
            if not isinstance(env_oracle, str) or not env_oracle.strip():
                raise ValueError("missing_oracle_pubkey")
            oracle_pubkey = _canonical_pubkey(env_oracle, name="oracle_pubkey")
        oracle_nonce = _nonce_for_signer(body, app_state=app_state, field="oracle_nonce", signer_pubkey=oracle_pubkey)
        operation = {
            "module": "TauPerp",
            "version": "1.2" if is_chnp_market else "1.0",
            "market_id": market_id,
            "action": action,
            "price_e8": _request_positive_int(body, name="price_e8"),
            "deadline": int(deadline),
            "oracle_nonce": oracle_nonce,
        }
        operation["oracle_sig"] = _sign_or_copy(
            body,
            op=operation,
            sig_field="oracle_sig",
            privkey_field="oracle_privkey",
            chain_id=chain_id,
            signer_pubkey=oracle_pubkey,
            nonce=oracle_nonce,
        )
        tx_sender = _tx_sender_for_action(body, action=action, account_a_pubkey=None, account_pubkey=oracle_pubkey)
        meta.update({"oracle_pubkey": oracle_pubkey, "oracle_nonce": oracle_nonce})
        return operation, tx_sender, meta

    if action == "submit_intent":
        account_pubkey = _account_pubkey(body, field="account_pubkey", privkey_field="account_privkey")
        tx_sender = _tx_sender_for_action(body, action=action, account_a_pubkey=None, account_pubkey=account_pubkey)
        now_epoch = _np_market_now_epoch(app_state, market_id=market_id)
        operation = {
            "module": "TauPerp",
            "version": "1.2",
            "market_id": market_id,
            "action": action,
            "account_pubkey": account_pubkey,
            "target_base": _request_int_alias(
                body,
                names=("target_base", "targetBase", "new_position_base", "newPositionBase"),
            ),
            "limit_price_e8": _request_int_alias(
                body,
                names=("limit_price_e8", "limitPriceE8"),
                default=0,
                non_negative=True,
            ),
            "min_fill_base": _request_int_alias(
                body,
                names=("min_fill_base", "minFillBase"),
                default=0,
                non_negative=True,
            ),
            "expiry_epoch": _request_int_alias(
                body,
                names=("expiry_epoch", "expiryEpoch"),
                default=now_epoch + 1,
                non_negative=True,
            ),
        }
        meta.update({"account_pubkey": account_pubkey})
        return operation, tx_sender, meta

    account_a_pubkey = _account_pubkey(body, field="account_a_pubkey", privkey_field="account_a_privkey")
    account_b_pubkey = _account_pubkey(body, field="account_b_pubkey", privkey_field="account_b_privkey")
    nonce_a = _nonce_for_signer(body, app_state=app_state, field="nonce_a", signer_pubkey=account_a_pubkey)
    nonce_b = _nonce_for_signer(body, app_state=app_state, field="nonce_b", signer_pubkey=account_b_pubkey)
    tx_sender = _tx_sender_for_action(body, action=action, account_a_pubkey=account_a_pubkey, account_pubkey=None)
    meta.update(
        {
            "account_a_pubkey": account_a_pubkey,
            "account_b_pubkey": account_b_pubkey,
            "nonce_a": nonce_a,
            "nonce_b": nonce_b,
        }
    )

    if action == "init_market_2p":
        operation = {
            "module": "TauPerp",
            "version": "1.0",
            "market_id": market_id,
            "action": action,
            "quote_asset": _quote_asset(body, chain_id=chain_id),
            "account_a_pubkey": account_a_pubkey,
            "account_b_pubkey": account_b_pubkey,
            "deadline": int(deadline),
            "nonce_a": nonce_a,
            "nonce_b": nonce_b,
        }
    else:
        new_a = _request_int(body, name="new_position_base_a")
        new_b = _request_int(body, name="new_position_base_b", default=-new_a)
        operation = {
            "module": "TauPerp",
            "version": "1.0",
            "market_id": market_id,
            "action": action,
            "account_a_pubkey": account_a_pubkey,
            "account_b_pubkey": account_b_pubkey,
            "new_position_base_a": new_a,
            "new_position_base_b": new_b,
            "deadline": int(deadline),
            "nonce_a": nonce_a,
            "nonce_b": nonce_b,
        }

    operation["sig_a"] = _sign_or_copy(
        body,
        op=operation,
        sig_field="sig_a",
        privkey_field="account_a_privkey",
        chain_id=chain_id,
        signer_pubkey=account_a_pubkey,
        nonce=nonce_a,
    )
    operation["sig_b"] = _sign_or_copy(
        body,
        op=operation,
        sig_field="sig_b",
        privkey_field="account_b_privkey",
        chain_id=chain_id,
        signer_pubkey=account_b_pubkey,
        nonce=nonce_b,
    )
    return operation, tx_sender, meta


def _default_oracle_adapter_bridge_verifier(bridge: Mapping[str, Any]) -> Any:
    from tools.zenodex_oracle_aggregate_adapter import (  # pylint: disable=import-outside-toplevel
        verify_aggregate_adapter_bridge,
    )

    return verify_aggregate_adapter_bridge(bridge)


def _build_perp_config(*, chain_id: str) -> PerpEngineConfig:
    operator_pubkey = os.environ.get("TAU_DEX_OPERATOR_PUBKEY") or os.environ.get("TAU_DEX_PERP_OPERATOR_PUBKEY")
    oracle_pubkey = os.environ.get("TAU_DEX_PERP_ORACLE_PUBKEY") or os.environ.get("TAU_DEX_ORACLE_PUBKEY")
    return PerpEngineConfig(
        operator_pubkey=(operator_pubkey or "").strip() or None,
        chain_id=chain_id,
        oracle_pubkey=(oracle_pubkey or "").strip() or None,
        allow_isolated_markets=_env_bool("TAU_DEX_ALLOW_ISOLATED_PERPS", False),
        oracle_adapter_bridge_verifier=_default_oracle_adapter_bridge_verifier,
        require_oracle_adapter_for_clearinghouse_settle_epoch=_env_bool(
            "TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH",
            True,
        ),
        require_oracle_adapter_for_isolated_partial_liquidate=_env_bool(
            "TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_ISOLATED_PARTIAL_LIQUIDATE",
            True,
        ),
    )


def _preflight(
    *,
    app_state: Mapping[str, Any],
    config: PerpEngineConfig,
    operation: Mapping[str, Any],
    tx_sender_pubkey: str,
    block_timestamp: int,
) -> dict[str, Any]:
    try:
        state = _state_from_app_state(app_state)
        res = apply_perp_ops(
            config=config,
            state=state,
            operations={_ENGINE_STREAM_KEY: [dict(operation)]},
            tx_sender_pubkey=tx_sender_pubkey,
            block_timestamp=int(block_timestamp),
        )
        return {"ok": bool(res.ok), "error": res.error, "effects": list(res.effects or [])}
    except Exception as exc:
        return {"ok": False, "error": str(exc), "effects": []}


def _market_summaries(app_state: Mapping[str, Any]) -> list[dict[str, Any]]:
    state = _state_from_app_state(app_state)
    if state.perps is None:
        return []
    balance_index = _balance_index(app_state) if state.perps.markets else {}
    summaries: list[dict[str, Any]] = []
    for market_id, market in sorted(state.perps.markets.items()):
        item: dict[str, Any] = {"market_id": market_id, "kind": getattr(market, "kind", "unknown")}
        if isinstance(market, PerpClearinghouse2pMarketState):
            item.update(
                {
                    "quote_asset": market.quote_asset,
                    "account_a_pubkey": market.account_a_pubkey,
                    "account_b_pubkey": market.account_b_pubkey,
                    "account_a_quote_balance": _indexed_balance_for_asset(
                        balance_index,
                        pubkey=market.account_a_pubkey,
                        asset_id=market.quote_asset,
                    ),
                    "account_b_quote_balance": _indexed_balance_for_asset(
                        balance_index,
                        pubkey=market.account_b_pubkey,
                        asset_id=market.quote_asset,
                    ),
                    "now_epoch": int(market.state.get("now_epoch", 0)),
                    "clearing_price_seen": int(bool(market.state.get("clearing_price_seen", False))),
                    "oracle_last_update_epoch": int(market.state.get("oracle_last_update_epoch", 0)),
                    "clearing_price_epoch": int(market.state.get("clearing_price_epoch", 0)),
                    "clearing_price_e8": int(market.state.get("clearing_price_e8", 0)),
                    "index_price_e8": int(market.state.get("index_price_e8", 0)),
                    "position_base_a": int(market.state.get("position_base_a", 0)),
                    "position_base_b": int(market.state.get("position_base_b", 0)),
                    "collateral_e8_a": int(market.state.get("collateral_e8_a", 0)),
                    "collateral_e8_b": int(market.state.get("collateral_e8_b", 0)),
                    "fee_pool_e8": int(market.state.get("fee_pool_e8", 0)),
                    "liquidated_this_step": bool(market.state.get("liquidated_this_step", False)),
                    "net_deposited_e8": int(market.state.get("net_deposited_e8", 0)),
                    "maintenance_margin_bps": int(market.state.get("maintenance_margin_bps", 0)),
                    "liquidation_penalty_bps": int(market.state.get("liquidation_penalty_bps", 0)),
                }
            )
        elif isinstance(market, PerpClearinghouseNpMarketState):
            accounts = []
            long_count = 0
            short_count = 0
            active_count = 0
            net_position_base = 0
            for account in sorted(
                market.accounts,
                key=lambda acct: canonical_hex_fixed_allow_0x(acct.pubkey, nbytes=48, name="np account pubkey"),
            ):
                position_base = int(account.position_base)
                collateral_e8 = int(account.collateral_e8)
                if position_base > 0:
                    long_count += 1
                elif position_base < 0:
                    short_count += 1
                if position_base != 0 or collateral_e8 != 0:
                    active_count += 1
                net_position_base += position_base
                accounts.append(
                    {
                        "account_pubkey": account.pubkey,
                        "position_base": position_base,
                        "entry_price_e8": int(account.entry_price_e8),
                        "collateral_e8": collateral_e8,
                        "collateral_quote": collateral_e8 // 100_000_000,
                        "funding_paid_cum_e8": int(account.funding_paid_cum_e8),
                        "nonce": int(account.nonce),
                        "quote_balance": _indexed_balance_for_asset(
                            balance_index,
                            pubkey=account.pubkey,
                            asset_id=market.quote_asset,
                        ),
                    }
                )
            pending_intents = [
                {
                    "account_pubkey": intent.pubkey,
                    "target_base": int(intent.target_base),
                    "limit_price_e8": int(intent.limit_price_e8),
                    "min_fill_base": int(intent.min_fill_base),
                    "expiry_epoch": int(intent.expiry_epoch),
                    "nonce": int(intent.nonce),
                }
                for intent in sorted(
                    market.pending_intents,
                    key=lambda intent: canonical_hex_fixed_allow_0x(intent.pubkey, nbytes=48, name="np intent pubkey"),
                )
            ]
            item.update(
                {
                    "quote_asset": market.quote_asset,
                    "now_epoch": int(market.global_state.get("now_epoch", 0)),
                    "clearing_price_seen": int(market.global_state.get("clearing_price_seen", 0)),
                    "clearing_price_epoch": int(market.global_state.get("clearing_price_epoch", 0)),
                    "clearing_price_e8": int(market.global_state.get("clearing_price_e8", 0)),
                    "index_price_e8": int(market.global_state.get("index_price_e8", 0)),
                    "maintenance_margin_bps": int(market.global_state.get("maintenance_margin_bps", 0)),
                    "initial_margin_bps": int(market.global_state.get("initial_margin_bps", 0)),
                    "liquidation_penalty_bps": int(market.global_state.get("liquidation_penalty_bps", 0)),
                    "max_position_abs": int(market.global_state.get("max_position_abs", 0)),
                    "fee_pool_e8": int(market.global_state.get("fee_pool_e8", 0)),
                    "insurance_e8": int(market.global_state.get("insurance_e8", 0)),
                    "insurance_ext_e8": int(market.global_state.get("insurance_ext_e8", 0)),
                    "claims_paid_e8": int(market.global_state.get("claims_paid_e8", 0)),
                    "net_deposited_e8": int(market.global_state.get("net_deposited_e8", 0)),
                    "funding_rate_bps": int(market.global_state.get("funding_rate_bps", 0)),
                    "account_count": len(accounts),
                    "active_count": active_count,
                    "long_count": long_count,
                    "short_count": short_count,
                    "net_position_base": net_position_base,
                    "pending_intent_count": len(pending_intents),
                    "accounts": accounts,
                    "pending_intents": pending_intents,
                    "liquidated_this_step": False,
                }
            )
        elif isinstance(market, PerpMarketState):
            accounts = []
            for account_pubkey, account in sorted(market.accounts.items()):
                accounts.append(
                    {
                        "account_pubkey": account_pubkey,
                        "position_base": int(account.position_base),
                        "collateral_quote": int(account.collateral_quote),
                        "liquidated_this_step": bool(account.liquidated_this_step),
                        # Surface the account's funded quote-asset wallet balance,
                        # like the 2p/NP branches — otherwise _account_perps_view
                        # defaults it to 0 and a funded isolated-perp account shows a
                        # zero perps balance (Codex F5, sibling of the F4 2p fix).
                        "quote_balance": _indexed_balance_for_asset(
                            balance_index,
                            pubkey=account_pubkey,
                            asset_id=market.quote_asset,
                        ),
                    }
                )
            item.update(
                {
                    "quote_asset": market.quote_asset,
                    "now_epoch": int(market.global_state.get("now_epoch", 0)),
                    "index_price_e8": int(market.global_state.get("index_price_e8", 0)),
                    "fee_pool_quote": int(market.global_state.get("fee_pool_quote", 0)),
                    "fee_income": int(market.global_state.get("fee_income", 0)),
                    "initial_insurance": int(market.global_state.get("initial_insurance", 0)),
                    "insurance_balance": int(market.global_state.get("insurance_balance", 0)),
                    "claims_paid": int(market.global_state.get("claims_paid", 0)),
                    "account_count": len(accounts),
                    "accounts": accounts,
                }
            )
        summaries.append(item)
    return summaries


def _account_perps_view(markets: list[dict[str, Any]], account: str) -> dict[str, Any]:
    """Derive the connected account's positions/collateral/balances across markets.

    Reuses the already-built ``markets`` summaries (no extra Tau reads). The account
    is matched case-insensitively against the per-market account pubkeys. The returned
    view is what makes the perps surface account-aware in the same way the pool surface
    resolves balances for a connected wallet.
    """
    target = account.strip().lower()
    positions: list[dict[str, Any]] = []
    total_collateral_e8 = 0
    for market in markets:
        market_id = market.get("market_id")
        quote_asset = market.get("quote_asset")
        # Clearinghouse 2p markets expose account_a / account_b inline.
        for slot in ("a", "b"):
            slot_pubkey = market.get(f"account_{slot}_pubkey")
            if isinstance(slot_pubkey, str) and slot_pubkey.strip().lower() == target:
                collateral_e8 = int(market.get(f"collateral_e8_{slot}", 0))
                total_collateral_e8 += collateral_e8
                positions.append(
                    {
                        "market_id": market_id,
                        "quote_asset": quote_asset,
                        "kind": market.get("kind"),
                        "position_base": int(market.get(f"position_base_{slot}", 0)),
                        "collateral_e8": collateral_e8,
                        "quote_balance": int(market.get(f"account_{slot}_quote_balance", 0)),
                    }
                )
        # NP / isolated markets expose an accounts list.
        for account_entry in market.get("accounts", []) or []:
            if not isinstance(account_entry, Mapping):
                continue
            entry_pubkey = account_entry.get("account_pubkey")
            if isinstance(entry_pubkey, str) and entry_pubkey.strip().lower() == target:
                collateral_e8 = int(
                    account_entry.get("collateral_e8", account_entry.get("collateral_quote", 0))
                )
                total_collateral_e8 += collateral_e8
                positions.append(
                    {
                        "market_id": market_id,
                        "quote_asset": quote_asset,
                        "kind": market.get("kind"),
                        "position_base": int(account_entry.get("position_base", 0)),
                        "collateral_e8": collateral_e8,
                        "quote_balance": int(account_entry.get("quote_balance", 0)),
                    }
                )
    return {
        "account": account,
        "position_count": len(positions),
        "total_collateral_e8": total_collateral_e8,
        "positions": positions,
    }


def _local_perps_oracle_bridge_fixture(
    *,
    app_state: Mapping[str, Any],
    config: PerpEngineConfig,
    market_id: str,
    action: str,
    account_pubkey: str | None = None,
    fraction_bps: int = 0,
) -> dict[str, Any]:
    wallet_action = action
    from tools.zenodex_oracle import ACTION_TYPE, receipt_content_hash  # pylint: disable=import-outside-toplevel
    from tools.zenodex_oracle_adapter import (  # pylint: disable=import-outside-toplevel
        ACTION_SCHEMA,
        PROFILE_SCHEMA,
        profile_content_hash,
    )
    from tools.zenodex_oracle_admitted_median3 import (  # pylint: disable=import-outside-toplevel
        sample_admitted_median3_aggregate,
        verify_admitted_median3_aggregate,
    )
    from tools.zenodex_oracle_aggregate_adapter import (  # pylint: disable=import-outside-toplevel
        AGGREGATE_ADAPTER_SCHEMA,
        aggregate_adapter_content_hash,
        verify_aggregate_adapter_bridge,
    )
    from tools.zenodex_oracle_aggregate_read import (  # pylint: disable=import-outside-toplevel
        AGGREGATE_READ_SCHEMA,
        _bundle_for_aggregate,
        aggregate_read_value_hash,
        bridge_content_hash as aggregate_read_content_hash,
    )
    from .perp_engine import (  # pylint: disable=import-outside-toplevel
        _ORACLE_PERPS_INDEX_QUERY_ID,
        _ORACLE_PERPS_LIQUIDATE_ACCOUNT_PROFILE_ID,
        _ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
        _perps_clearinghouse_runtime_oracle_action_id,
        _perps_liquidate_account_runtime_oracle_action_id,
    )

    state = _state_from_app_state(app_state)
    if state.perps is None:
        raise ValueError("missing_perps_state")
    market = state.perps.get_market(market_id)
    if wallet_action in {"run_epoch", "settle_epoch"}:
        if isinstance(market, PerpClearinghouse2pMarketState):
            market_kind = "clearinghouse_2p_v1"
            quote_asset = market.quote_asset
            state_for_oracle = market.state
            participant_pubkeys = (market.account_a_pubkey, market.account_b_pubkey)
        elif isinstance(market, PerpClearinghouseNpMarketState):
            market_kind = "clearinghouse_np_v1"
            quote_asset = market.quote_asset
            state_for_oracle = market.global_state
            participant_pubkeys = tuple(
                account.pubkey
                for account in sorted(
                    market.accounts,
                    key=lambda acct: canonical_hex_fixed_allow_0x(acct.pubkey, nbytes=48, name="np account pubkey"),
                )
            )
        else:
            raise ValueError("settle oracle bridge fixture supports clearinghouse 2p/np markets only")
        action_kind = "settle_epoch"
        profile_id = _ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID
        freshness_window_epochs = 2
        action_id = _perps_clearinghouse_runtime_oracle_action_id(
            config,
            market_id=market_id,
            action_kind=action_kind,
            market_kind=market_kind,
            quote_asset=quote_asset,
            state=state_for_oracle,
            participant_pubkeys=participant_pubkeys,
        )
    elif wallet_action == "partial_liquidate":
        if not isinstance(market, PerpMarketState):
            raise ValueError("partial_liquidate oracle bridge fixture supports isolated markets only")
        if account_pubkey is None:
            raise ValueError("missing_account_pubkey")
        action_kind = "liquidate_account"
        profile_id = _ORACLE_PERPS_LIQUIDATE_ACCOUNT_PROFILE_ID
        freshness_window_epochs = 1
        action_id = _perps_liquidate_account_runtime_oracle_action_id(
            config,
            market_id=market_id,
            market=market,
            account_pubkey=account_pubkey,
            fraction_bps=fraction_bps,
        )
    else:
        raise ValueError("unsupported_oracle_bridge_action")

    aggregate = sample_admitted_median3_aggregate()
    aggregate_result = verify_admitted_median3_aggregate(aggregate)
    if aggregate_result.status != "accepted":
        raise ValueError("local oracle aggregate fixture rejected")
    if aggregate_result.query_id != _ORACLE_PERPS_INDEX_QUERY_ID:
        raise ValueError("local oracle aggregate fixture query mismatch")

    value_hash = aggregate_read_value_hash(
        aggregate_id=str(aggregate_result.aggregate_id),
        query_id=str(aggregate_result.query_id),
        value_e8=int(aggregate_result.value_e8),
        confidence_e8=int(aggregate_result.confidence_e8),
        deviation_bps=int(aggregate_result.deviation_bps),
        observed_epoch=int(aggregate_result.observed_epoch),
        report_count=int(aggregate_result.report_count),
        admission_count=int(aggregate_result.admission_count),
    )
    bundle = _bundle_for_aggregate(
        aggregate_id=str(aggregate_result.aggregate_id),
        query_id=str(aggregate_result.query_id),
        value_hash=value_hash,
        observed_epoch=int(aggregate_result.observed_epoch),
        freshness_window_epochs=freshness_window_epochs,
    )
    read_receipt_id = str(bundle["terminal"]["read_receipt_id"])
    read_receipt = next(
        receipt
        for receipt in bundle["receipts"]
        if isinstance(receipt, Mapping) and receipt.get("id") == read_receipt_id
    )
    action_epoch = int(aggregate_result.observed_epoch) + 1
    action_receipt: dict[str, Any] = {
        "type": ACTION_TYPE,
        "status": "accepted",
        "consumer_module": "zenodex.perps",
        "action_kind": action_kind,
        "action_id": action_id,
        "action_epoch": action_epoch,
        "freshness_window_epochs": freshness_window_epochs,
        "query_id": str(aggregate_result.query_id),
        "value_hash": value_hash,
        "read_receipt_id": read_receipt_id,
        "critical": True,
        "emergency_oracle_bypass": False,
        "depends_on": [read_receipt_id],
    }
    action_receipt["id"] = receipt_content_hash(action_receipt)
    bundle["receipts"] = [dict(read_receipt), action_receipt]
    bundle["terminal"]["consumer_action_receipt_id"] = action_receipt["id"]

    aggregate_read: dict[str, Any] = {
        "schema": AGGREGATE_READ_SCHEMA,
        "freshness_window_epochs": freshness_window_epochs,
        "aggregate": dict(aggregate),
        "receipt_bundle": bundle,
    }
    aggregate_read["bridge_id"] = aggregate_read_content_hash(aggregate_read)

    adapter_action = {
        "schema": ACTION_SCHEMA,
        "consumer_module": "zenodex.perps",
        "action_kind": action_kind,
        "action_id": action_id,
        "action_epoch": action_epoch,
        "query_id": str(aggregate_result.query_id),
        "value_hash": value_hash,
        "required_evidence_floor": "O3",
        "max_freshness_window_epochs": freshness_window_epochs,
        "read_receipt_id": read_receipt_id,
        "consumer_action_receipt_id": action_receipt["id"],
        "critical": True,
    }
    profile = {
        "schema": PROFILE_SCHEMA,
        "consumer_module": "zenodex.perps",
        "action_kind": action_kind,
        "query_id": str(aggregate_result.query_id),
        "required_evidence_floor": "O3",
        "max_freshness_window_epochs": freshness_window_epochs,
        "critical": True,
    }
    profile["profile_id"] = profile_content_hash(profile)
    if profile["profile_id"] != profile_id:
        raise ValueError("local oracle profile fixture mismatch")

    bridge = {
        "schema": AGGREGATE_ADAPTER_SCHEMA,
        "aggregate_read": aggregate_read,
        "action": adapter_action,
        "profile": profile,
    }
    bridge["bridge_id"] = aggregate_adapter_content_hash(bridge)
    verify_result = verify_aggregate_adapter_bridge(bridge).to_json_obj()
    if verify_result.get("status") != "accepted":
        raise ValueError(f"local oracle bridge fixture rejected: {verify_result.get('errors')}")
    return {
        "schema": "zenodex.perps_wallet.oracle_bridge_fixture.v1",
        "ok": True,
        "fixture_kind": "local_o3_aggregate_adapter",
        "production_authority": False,
        "market_id": market_id,
        "action": wallet_action,
        "target": {
            "query_id": _ORACLE_PERPS_INDEX_QUERY_ID,
            "profile_id": profile_id,
            "action_id": action_id,
            "consumer_module": "zenodex.perps",
            "action_kind": action_kind,
            "wallet_action": wallet_action,
        },
        "bridge": bridge,
        "verify_result": verify_result,
    }


def _oracle_adapter_bridge_from_body(body: Mapping[str, Any]) -> Mapping[str, Any]:
    bridge = _request_mapping(body, name="oracle_adapter_bridge")
    if bridge is None:
        bridge = _request_mapping(body, name="bridge")
    if bridge is None and str(body.get("schema", "")).strip() == "zenodex.oracle.aggregate_adapter_bridge.v1":
        bridge = body
    if bridge is None:
        raise ValueError("missing_oracle_adapter_bridge")
    return bridge


def _inspect_oracle_adapter_bridge(body: Mapping[str, Any]) -> dict[str, Any]:
    from tools.zenodex_oracle_aggregate_adapter import (  # pylint: disable=import-outside-toplevel
        verify_aggregate_adapter_bridge,
    )

    bridge = _oracle_adapter_bridge_from_body(body)
    verify_result = verify_aggregate_adapter_bridge(bridge).to_json_obj()
    aggregate_read = bridge.get("aggregate_read")
    if not isinstance(aggregate_read, Mapping):
        aggregate_read = {}
    aggregate = aggregate_read.get("aggregate")
    if not isinstance(aggregate, Mapping):
        aggregate = {}
    aggregate_value = aggregate.get("aggregate")
    if not isinstance(aggregate_value, Mapping):
        aggregate_value = {}
    action = bridge.get("action")
    if not isinstance(action, Mapping):
        action = {}
    profile = bridge.get("profile")
    if not isinstance(profile, Mapping):
        profile = {}
    receipt_bundle = aggregate_read.get("receipt_bundle")
    terminal = receipt_bundle.get("terminal") if isinstance(receipt_bundle, Mapping) else {}
    if not isinstance(terminal, Mapping):
        terminal = {}

    summary = {
        "bridge_id": bridge.get("bridge_id"),
        "consumer_module": action.get("consumer_module"),
        "action_kind": action.get("action_kind"),
        "action_id": action.get("action_id"),
        "action_epoch": action.get("action_epoch"),
        "query_id": action.get("query_id") or aggregate.get("query_id"),
        "profile_id": profile.get("profile_id"),
        "required_evidence_floor": action.get("required_evidence_floor") or profile.get("required_evidence_floor"),
        "max_freshness_window_epochs": action.get("max_freshness_window_epochs")
        or profile.get("max_freshness_window_epochs"),
        "read_receipt_id": action.get("read_receipt_id") or terminal.get("read_receipt_id"),
        "consumer_action_receipt_id": action.get("consumer_action_receipt_id")
        or terminal.get("consumer_action_receipt_id"),
        "aggregate_id": aggregate.get("aggregate_id"),
        "value_e8": aggregate_value.get("value_e8"),
        "confidence_e8": aggregate_value.get("confidence_e8"),
        "deviation_bps": aggregate_value.get("deviation_bps"),
        "observed_epoch": aggregate_value.get("observed_epoch"),
        "report_count": aggregate_value.get("report_count"),
        "evidence_class": aggregate.get("evidence_class") or aggregate.get("evidence_floor"),
        "production_authority": False,
    }
    return {
        "schema": "zenodex.perps_wallet.oracle_bridge_inspection.v1",
        "ok": verify_result.get("status") == "accepted",
        "status": verify_result.get("status"),
        "summary": summary,
        "verify_result": verify_result,
        "production_authority": False,
    }


def _tx_signer_privkey(body: Mapping[str, Any], *, action: str) -> object:
    privkey = body.get("tx_signer_privkey")
    if privkey is not None:
        return privkey
    if action in {
        "join_market",
        "deposit_collateral",
        "withdraw_collateral",
        "deposit_insurance",
        "submit_intent",
        "partial_liquidate",
    } and body.get("account_privkey") is not None:
        return body.get("account_privkey")
    if action == "publish_clearing_price" and body.get("oracle_privkey") is not None:
        return body.get("oracle_privkey")
    if action in {"init_market_np", "advance_epoch", "run_epoch", "settle_epoch"} and body.get("operator_privkey") is not None:
        return body.get("operator_privkey")
    if body.get("account_a_privkey") is not None:
        return body.get("account_a_privkey")
    if body.get("signer_privkey") is not None:
        return body.get("signer_privkey")
    raise ValueError("missing_tx_signer_privkey")


def _testnet_faucet_signer_privkey(body: Mapping[str, Any]) -> object:
    for key in ("signer_privkey", "account_privkey", "operator_privkey", "tx_signer_privkey"):
        value = body.get(key)
        if value is not None:
            return value
    raise ValueError("missing_signer_privkey")


def _build_testnet_faucet_response(body: Mapping[str, Any]) -> Dict[str, Any]:
    if not _testnet_faucet_enabled():
        raise ValueError("perps_wallet_testnet_faucet_disabled")

    chain_id = str(body.get("chain_id") or _tau_chain_id())
    to_pubkey = _canonical_pubkey(body.get("to_pubkey", body.get("account_pubkey")), name="to_pubkey")
    asset = _canonical_asset(body.get("asset", body.get("quote_asset", body.get("quoteAsset"))), name="asset")
    amount = _request_positive_int(body, name="amount")
    max_amount = _testnet_faucet_max_amount()
    if amount > max_amount:
        raise ValueError(f"testnet_faucet_amount_exceeds_cap:{amount}>{max_amount}")
    tx_fee_limit = _request_tx_fee_limit(body)
    deadline = _request_u32(body, name="deadline", default=_default_deadline())
    signer_privkey = _testnet_faucet_signer_privkey(body)
    signer_pubkey = _canonical_pubkey(_pubkey_from_privkey(signer_privkey), name="signer_pubkey")
    authority_pubkey = _testnet_faucet_authority_pubkey()
    if signer_pubkey.lower() != authority_pubkey.lower():
        raise ValueError("testnet_faucet_authority_mismatch")

    client = _tau_client()
    app_state_before, app_hash_before = _load_app_state(client)
    balance_before = _balance_for_asset(app_state_before, pubkey=to_pubkey, asset_id=asset)
    tx_sequence_number = int(client.get_sequence(_pubkey_for_rpc(signer_pubkey)))
    operations = {"14": {"mint": [{"pubkey": to_pubkey, "asset": asset, "amount": amount}]}}
    tau_tx_payload = build_signed_tau_transaction(
        privkey=cast(Any, signer_privkey),
        sequence_number=tx_sequence_number,
        expiration_time=deadline,
        operations=operations,
        fee_limit=tx_fee_limit,
    )
    send_resp = client.sendtx(tau_tx_payload)
    submission: Dict[str, Any] = {"sendtx_response": send_resp}
    if not tau_rpc_response_is_success(send_resp):
        invalid_sequence = _invalid_sequence_numbers(send_resp)
        if (
            invalid_sequence is not None
            and int(invalid_sequence[1]) == int(tx_sequence_number)
            and int(invalid_sequence[0]) > int(tx_sequence_number)
        ):
            tx_sequence_number = int(invalid_sequence[0])
            submission["retry_sequence_error"] = {
                "expected": int(invalid_sequence[0]),
                "got": int(invalid_sequence[1]),
            }
            tau_tx_payload = build_signed_tau_transaction(
                privkey=cast(Any, signer_privkey),
                sequence_number=tx_sequence_number,
                expiration_time=deadline,
                operations=operations,
                fee_limit=tx_fee_limit,
            )
            retry_send_resp = client.sendtx(tau_tx_payload)
            submission["retry_sendtx_response"] = retry_send_resp
            send_resp = retry_send_resp
        if tau_rpc_response_is_success(send_resp):
            pass
        else:
            return {
                "ok": False,
                "error": "sendtx_failed",
                "status": "submit_rejected",
                "submission": submission,
                "testnet_only": True,
                "production_authority": False,
            }

    if _auto_mine():
        createblock_resp = client.createblock()
        submission["createblock_response"] = createblock_resp
        if not tau_rpc_response_is_success(createblock_resp):
            observed_state, observed_hash = _wait_for_app_hash_change(client, app_hash_before)
            observed_balance = _balance_for_asset(observed_state, pubkey=to_pubkey, asset_id=asset)
            submission["observed_app_hash_after_createblock"] = observed_hash
            submission["observed_balance_after_createblock"] = observed_balance
            if observed_balance <= balance_before:
                submission["createblock_empty_without_balance_delta"] = True

    app_state_after, app_hash_after = _load_app_state(client)
    balance_after = _balance_for_asset(app_state_after, pubkey=to_pubkey, asset_id=asset)
    if balance_after < balance_before + amount:
        return {
            "ok": False,
            "error": "faucet_balance_delta_missing",
            "status": "submit_indeterminate",
            "submission": submission,
            "testnet_only": True,
            "production_authority": False,
            "balance_before": balance_before,
            "balance_after": balance_after,
            "expected_balance_after_at_least": balance_before + amount,
            "app_hash_before": app_hash_before,
            "app_hash_after": app_hash_after,
        }
    return _redact_response_authority_material({
        "ok": True,
        "schema": "zenodex/perps-wallet-testnet-faucet/v1",
        "testnet_only": True,
        "production_authority": False,
        "chain_id": chain_id,
        "to_pubkey": to_pubkey,
        "asset": asset,
        "amount": amount,
        "balance_before": balance_before,
        "balance_after": balance_after,
        "app_hash_before": app_hash_before,
        "app_hash_after": app_hash_after,
        "transport": {
            "stream_key": "21",
            "tx_sender_pubkey": signer_pubkey,
            "testnet_faucet_authority_pubkey": authority_pubkey,
            "tx_sequence_number": tx_sequence_number,
            "tx_fee_limit": str(tx_fee_limit),
            "auto_mine": _auto_mine(),
        },
        "report": {
            "operations": operations,
            "tau_tx_payload": tau_tx_payload,
        },
        "submission": submission,
    })


def _build_prepare_response(body: Mapping[str, Any], *, for_submit: bool) -> Dict[str, Any]:
    action = _request_action(body)
    chain_id = str(body.get("chain_id") or _tau_chain_id())
    deadline = _request_u32(body, name="deadline", default=_default_deadline())
    client = _tau_client()
    app_state, app_hash = _load_app_state(client)
    config = _build_perp_config(chain_id=chain_id)
    operation, tx_sender_pubkey, meta = _build_operation_and_sender(
        body,
        action=action,
        app_state=app_state,
        chain_id=chain_id,
        deadline=deadline,
    )
    native_balance = _safe_native_balance(client, tx_sender_pubkey)
    tx_fee_limit = _request_tx_fee_limit(body)
    fee_limit_posture = _fee_limit_posture(tx_fee_limit=tx_fee_limit, native_balance=native_balance)
    operations = {_STREAM_KEY: [operation]}
    tx_sequence_number = int(client.get_sequence(_pubkey_for_rpc(tx_sender_pubkey)))
    block_timestamp = int(time.time())
    preflight = _preflight(
        app_state=app_state,
        config=config,
        operation=operation,
        tx_sender_pubkey=tx_sender_pubkey,
        block_timestamp=block_timestamp,
    )
    if for_submit and not preflight.get("ok"):
        raise ValueError(f"preflight_failed: {preflight.get('error') or 'unknown'}")
    oracle_authority_exercise = _oracle_authority_exercise_for_action(
        action=action,
        chain_id=chain_id,
        operation=operation,
    )
    if (
        oracle_authority_exercise is not None
        and oracle_authority_exercise.get("required_for_action") is True
        and oracle_authority_exercise.get("authority_exercised") is not True
    ):
        gaps = ", ".join(str(gap) for gap in oracle_authority_exercise.get("readiness_gaps", []))
        raise ValueError(f"production_oracle_authority_required: {gaps or 'authority not exercised'}")
    quote_asset = str(operation.get("quote_asset") or body.get("quote_asset") or body.get("quoteAsset") or "")
    if not quote_asset:
        quote_asset = _market_quote_asset(app_state, market_id=_market_id(body, action=action))
    account_pubkey = str(operation.get("account_pubkey") or meta.get("account_a_pubkey") or tx_sender_pubkey)
    quote_balance = _balance_for_asset(app_state, pubkey=account_pubkey, asset_id=quote_asset) if quote_asset else 0

    tau_tx_payload: dict[str, Any] | None = None
    local_signer_privkey: object | None = None
    signing_mode = "prepare_only"
    if for_submit:
        external_payload = _request_signed_tau_tx_payload(body)
        if external_payload is not None:
            tau_tx_payload = _validate_external_tau_tx_payload(
                external_payload,
                tx_sender_pubkey=tx_sender_pubkey,
                tx_sequence_number=tx_sequence_number,
                deadline=deadline,
                operations=operations,
                tx_fee_limit=tx_fee_limit,
            )
            signing_mode = "external_signed_payload"
        else:
            if not _allow_signing():
                raise ValueError("local_signing_disabled")
            signer_privkey = _tx_signer_privkey(body, action=action)
            signer_pubkey = _canonical_pubkey(_pubkey_from_privkey(signer_privkey), name="tx_signer_pubkey")
            if signer_pubkey.lower() != tx_sender_pubkey.lower():
                raise ValueError("tx_signer_privkey does not match sender_pubkey")
            local_signer_privkey = signer_privkey
            tau_tx_payload = build_signed_tau_transaction(
                privkey=cast(Any, signer_privkey),
                sequence_number=tx_sequence_number,
                expiration_time=deadline,
                operations=operations,
                fee_limit=tx_fee_limit,
            )
            signing_mode = "local_test_signing"

    payload: Dict[str, Any] = {
        "ok": True,
        "transport": {
            "chain_id": chain_id,
            "app_hash": app_hash,
            "stream_key": _STREAM_KEY,
            "engine_stream_key": _ENGINE_STREAM_KEY,
            "tx_sender_pubkey": tx_sender_pubkey,
            "tx_sequence_number": tx_sequence_number,
            "native_balance_e8": native_balance,
            "tx_fee_limit": str(tx_fee_limit),
            "fee_limit_native_balance_ok": fee_limit_posture["native_balance_covers_fee_limit"],
            "fee_limit_warning": fee_limit_posture["warning"],
            "tau_host": _env_str("PERPS_WALLET_TAU_HOST", _env_str("ZUSD_MONETARY_WALLET_TAU_HOST", "127.0.0.1")),
            "tau_port": _env_int(
                "PERPS_WALLET_TAU_PORT",
                _env_int("ZUSD_MONETARY_WALLET_TAU_PORT", 65432, lo=1, hi=65535),
                lo=1,
                hi=65535,
            ),
            "allow_local_signing": _allow_signing(),
            "signing_mode": signing_mode,
            "auto_mine": _auto_mine(),
            "quote_balance": quote_balance,
        },
        "report": {
            "action": action,
            "operation": operation,
            "operations": operations,
            "preflight": preflight,
            "fee_limit": fee_limit_posture,
            "tau_tx_payload": tau_tx_payload,
            "nonce_a": meta.get("nonce_a"),
            "nonce_b": meta.get("nonce_b"),
            "oracle_nonce": meta.get("oracle_nonce"),
        },
        "proof": {
            "profile": _perps_proof_profile(),
            "intent_receipt": _perps_proof_intent_receipt(
                chain_id=chain_id,
                action=action,
                operation=operation,
                operations=operations,
                app_hash_before=app_hash,
                app_hash_after=None,
                preflight=preflight,
                tx_sender_pubkey=tx_sender_pubkey,
                tx_sequence_number=tx_sequence_number,
                tx_fee_limit=tx_fee_limit,
                signing_mode=signing_mode,
                tau_tx_payload=tau_tx_payload,
                oracle_authority_exercise=oracle_authority_exercise,
                state_delta_witness=None,
            ),
            "oracle_authority_exercise": oracle_authority_exercise,
        },
    }
    zk_required = live_zk_proof_required(env_prefix=_PERPS_ZK_PROOF_ENV_PREFIX)
    payload = _bind_live_zk_wrapper(payload, body=body, required=zk_required)
    if for_submit:
        send_resp = client.sendtx(cast(Mapping[str, Any], tau_tx_payload))
        payload["submission"] = {"sendtx_response": send_resp}
        if not tau_rpc_response_is_success(send_resp):
            invalid_sequence = _invalid_sequence_numbers(send_resp)
            if (
                signing_mode == "local_test_signing"
                and local_signer_privkey is not None
                and invalid_sequence is not None
                and int(invalid_sequence[1]) == int(tx_sequence_number)
                and int(invalid_sequence[0]) > int(tx_sequence_number)
            ):
                if zk_required:
                    payload["submission"]["retry_sequence_error"] = {
                        "expected": int(invalid_sequence[0]),
                        "got": int(invalid_sequence[1]),
                    }
                    return _reject_payload(
                        payload,
                        status="submit_rejected",
                        error="sequence_retry_requires_fresh_zk_proof",
                    )
                tx_sequence_number = int(invalid_sequence[0])
                payload["submission"]["retry_sequence_error"] = {
                    "expected": int(invalid_sequence[0]),
                    "got": int(invalid_sequence[1]),
                }
                tau_tx_payload = build_signed_tau_transaction(
                    privkey=cast(Any, local_signer_privkey),
                    sequence_number=tx_sequence_number,
                    expiration_time=deadline,
                    operations=operations,
                    fee_limit=tx_fee_limit,
                )
                payload["transport"]["tx_sequence_number"] = tx_sequence_number
                payload["report"]["tau_tx_payload"] = tau_tx_payload
                retry_send_resp = client.sendtx(tau_tx_payload)
                payload["submission"]["retry_sendtx_response"] = retry_send_resp
                send_resp = retry_send_resp
            if tau_rpc_response_is_success(send_resp):
                pass
            else:
                return _reject_payload(payload, status="submit_rejected", error="sendtx_failed")
        if _auto_mine():
            createblock_response = client.createblock()
            payload["submission"]["createblock_response"] = createblock_response
            if not tau_rpc_response_is_success(createblock_response):
                _observed_state, observed_hash = _wait_for_app_hash_change(client, app_hash)
                payload["submission"]["observed_app_hash_after_createblock"] = observed_hash
                if observed_hash == app_hash:
                    if "mempool is empty" in str(createblock_response).lower():
                        retry_send_response = client.sendtx(tau_tx_payload)
                        payload["submission"]["retry_sendtx_response"] = retry_send_response
                        if tau_rpc_response_is_success(retry_send_response):
                            retry_createblock_response = client.createblock()
                            payload["submission"]["retry_createblock_response"] = retry_createblock_response
                            if tau_rpc_response_is_success(retry_createblock_response):
                                pass
                            else:
                                _retry_observed_state, retry_observed_hash = _wait_for_app_hash_change(client, app_hash)
                                payload["submission"]["retry_observed_app_hash_after_createblock"] = retry_observed_hash
                                if retry_observed_hash == app_hash:
                                    return _reject_payload(payload, status="submit_rejected", error="createblock_failed")
                        else:
                            _late_state, late_hash = _wait_for_app_hash_change(client, app_hash)
                            payload["submission"]["late_observed_app_hash_after_retry"] = late_hash
                            if late_hash is not None and late_hash != app_hash:
                                pass
                            else:
                                invalid_sequence = _invalid_sequence_numbers(retry_send_response)
                                if invalid_sequence is not None:
                                    expected_sequence, got_sequence = invalid_sequence
                                    payload["submission"]["retry_sequence_error"] = {
                                        "expected": expected_sequence,
                                        "got": got_sequence,
                                    }
                                payload["submission"]["observed_sequence_after_retry"] = _safe_sequence_after_submission(
                                    client,
                                    tx_sender_pubkey,
                                )
                                if (
                                    invalid_sequence is not None
                                    and int(invalid_sequence[1]) == int(tx_sequence_number)
                                    and int(invalid_sequence[0]) > int(tx_sequence_number)
                                ) or (
                                    "invalid sequence number" in str(retry_send_response).lower()
                                    and payload["submission"]["observed_sequence_after_retry"] is not None
                                    and int(payload["submission"]["observed_sequence_after_retry"]) > tx_sequence_number
                                ):
                                    return _reject_payload(
                                        payload,
                                        status="submit_indeterminate",
                                        error="tau_sequence_consumed_without_app_delta",
                                    )
                                return _reject_payload(payload, status="submit_rejected", error="sendtx_retry_failed")
                    else:
                        return _reject_payload(payload, status="submit_rejected", error="createblock_failed")
                elif observed_hash is None:
                    return _reject_payload(payload, status="submit_rejected", error="createblock_failed")
        app_state_after, app_hash_after = _load_app_state(client)
        state_delta_witness = _perps_state_delta_witness(
            chain_id=chain_id,
            action=action,
            operation=operation,
            app_hash_before=app_hash,
            app_hash_after=app_hash_after,
            app_state_before=app_state,
            app_state_after=app_state_after,
        )
        if not _state_delta_witness_matches_operation(state_delta_witness, operation):
            payload["post_submit"] = {
                "app_hash": app_hash_after,
                "markets": _market_summaries(app_state_after),
                "state_delta_witness": state_delta_witness,
            }
            return _reject_payload(
                payload,
                status="submit_indeterminate",
                error="state_delta_witness_missing",
            )
        payload["post_submit"] = {
            "app_hash": app_hash_after,
            "markets": _market_summaries(app_state_after),
            "state_delta_witness": state_delta_witness,
        }
        payload["proof"]["intent_receipt"] = _perps_proof_intent_receipt(
            chain_id=chain_id,
            action=action,
            operation=operation,
            operations=operations,
            app_hash_before=app_hash,
            app_hash_after=app_hash_after,
            preflight=preflight,
            tx_sender_pubkey=tx_sender_pubkey,
            tx_sequence_number=tx_sequence_number,
            tx_fee_limit=tx_fee_limit,
            signing_mode=signing_mode,
            tau_tx_payload=tau_tx_payload,
            oracle_authority_exercise=oracle_authority_exercise,
            state_delta_witness=state_delta_witness,
        )
        payload["proof"]["oracle_authority_exercise"] = oracle_authority_exercise
        payload = _bind_live_zk_wrapper(
            payload,
            body=body,
            required=zk_required,
            enforce_required=False,
            wrapper_key="post_submit_zk_wrapper",
        )
    return _redact_response_authority_material(payload)


def _status_payload(account: str | None = None) -> Dict[str, Any]:
    chain_id = _tau_chain_id()
    wallet_authority_profile, wallet_authority_error = _wallet_authority_profile_from_env()
    wallet_authority = evaluate_perps_wallet_authority_profile_v1(
        wallet_authority_profile,
        expected_chain_id=chain_id,
    )
    if wallet_authority_error is not None:
        wallet_authority["ok"] = False
        wallet_authority["production_wallet_authority"] = False
        wallet_authority["status"] = "blocked"
        wallet_authority.setdefault("readiness_gaps", []).append(wallet_authority_error)
    recovery_exercise, recovery_exercise_error = _wallet_recovery_exercise_from_env()
    if recovery_exercise is not None:
        wallet_authority["recovery_exercise"] = evaluate_perps_wallet_recovery_exercise_v1(
            wallet_authority_profile,
            recovery_exercise,
            expected_chain_id=chain_id,
        )
    elif recovery_exercise_error is not None:
        wallet_authority["recovery_exercise"] = {
            "schema": "zenodex/perps-wallet-recovery-exercise-status/v1",
            "ok": False,
            "recovery_exercise_ready": False,
            "status": "blocked",
            "errors": [recovery_exercise_error],
            "wallet_authority_hash": None if wallet_authority_profile is None else wallet_authority_profile.get("wallet_authority_hash"),
            "exercise_hash": None,
            "evaluation": None,
            "evaluation_hash": None,
        }
    rotation_exercise, rotation_exercise_error = _wallet_rotation_exercise_from_env()
    if rotation_exercise is not None:
        wallet_authority["rotation_exercise"] = evaluate_perps_wallet_rotation_exercise_v1(
            wallet_authority_profile,
            rotation_exercise,
            expected_chain_id=chain_id,
        )
    elif rotation_exercise_error is not None:
        wallet_authority["rotation_exercise"] = {
            "schema": "zenodex/perps-wallet-rotation-exercise-status/v1",
            "ok": False,
            "rotation_exercise_ready": False,
            "status": "blocked",
            "errors": [rotation_exercise_error],
            "wallet_authority_hash": None if wallet_authority_profile is None else wallet_authority_profile.get("wallet_authority_hash"),
            "exercise_hash": None,
            "current_wallet_authority_hash": None,
            "next_wallet_authority_hash": None,
        }
    device_approval_exercise, device_approval_exercise_error = _wallet_device_approval_exercise_from_env()
    if device_approval_exercise is not None:
        wallet_authority["device_approval_exercise"] = evaluate_perps_wallet_device_approval_exercise_v1(
            wallet_authority_profile,
            device_approval_exercise,
            expected_chain_id=chain_id,
        )
    elif device_approval_exercise_error is not None:
        wallet_authority["device_approval_exercise"] = {
            "schema": "zenodex/perps-wallet-device-approval-exercise-status/v1",
            "ok": False,
            "device_approval_ready": False,
            "status": "blocked",
            "errors": [device_approval_exercise_error],
            "wallet_authority_hash": None if wallet_authority_profile is None else wallet_authority_profile.get("wallet_authority_hash"),
            "exercise_hash": None,
            "sign_admission_receipt": None,
            "sign_admission_receipt_hash": None,
        }
    signer_device_integration, signer_device_integration_error = _wallet_signer_device_integration_from_env()
    if signer_device_integration is not None:
        wallet_authority["signer_device_integration"] = evaluate_perps_wallet_signer_device_integration_v1(
            wallet_authority_profile,
            signer_device_integration,
            expected_chain_id=chain_id,
        )
    elif signer_device_integration_error is not None:
        wallet_authority["signer_device_integration"] = {
            "schema": "zenodex/perps-wallet-signer-device-integration-status/v1",
            "ok": False,
            "signer_device_ready": False,
            "status": "blocked",
            "errors": [signer_device_integration_error],
            "wallet_authority_hash": None if wallet_authority_profile is None else wallet_authority_profile.get("wallet_authority_hash"),
            "integration_hash": None,
            "backend_hash": None,
            "environment_hash": None,
            "environment_policy_hash": None,
        }
    signer_prompt_capture, signer_prompt_capture_error = _wallet_signer_prompt_capture_from_env()
    if signer_prompt_capture is not None:
        wallet_authority["signer_prompt_capture"] = evaluate_perps_wallet_signer_prompt_capture_v1(
            wallet_authority_profile,
            signer_prompt_capture,
            expected_chain_id=chain_id,
        )
    elif signer_prompt_capture_error is not None:
        wallet_authority["signer_prompt_capture"] = {
            "schema": "zenodex/perps-wallet-signer-prompt-capture-status/v1",
            "ok": False,
            "signer_prompt_capture_ready": False,
            "status": "blocked",
            "errors": [signer_prompt_capture_error],
            "wallet_authority_hash": None if wallet_authority_profile is None else wallet_authority_profile.get("wallet_authority_hash"),
            "capture_hash": None,
            "backend_hash": None,
            "environment_hash": None,
            "environment_policy_hash": None,
        }
    signer_execution_exercise, signer_execution_exercise_error = _wallet_signer_execution_exercise_from_env()
    if signer_execution_exercise is not None:
        wallet_authority["signer_execution_exercise"] = evaluate_perps_wallet_signer_execution_exercise_v1(
            wallet_authority_profile,
            signer_execution_exercise,
            expected_chain_id=chain_id,
        )
    elif signer_execution_exercise_error is not None:
        wallet_authority["signer_execution_exercise"] = {
            "schema": "zenodex/perps-wallet-signer-execution-exercise-status/v1",
            "ok": False,
            "signer_execution_ready": False,
            "status": "blocked",
            "errors": [signer_execution_exercise_error],
            "wallet_authority_hash": None if wallet_authority_profile is None else wallet_authority_profile.get("wallet_authority_hash"),
            "exercise_hash": None,
            "backend_hash": None,
            "environment_hash": None,
            "use_policy_hash": None,
            "environment_policy_hash": None,
        }
    if any(
        key in wallet_authority
        for key in (
            "device_approval_exercise",
            "signer_device_integration",
            "signer_prompt_capture",
            "signer_execution_exercise",
        )
    ):
        production_hardware_evidence, production_hardware_evidence_error = _wallet_production_hardware_evidence_from_env()
        production_hardware_evidence_status = evaluate_production_hardware_wallet_evidence_v1(
            production_hardware_evidence,
            wallet_authority_profile_hash=None
            if wallet_authority_profile is None
            else wallet_authority_profile.get("wallet_authority_hash"),
            expected_device_pubkey=None,
        )
        if production_hardware_evidence_error is not None:
            production_hardware_evidence_status["ok"] = False
            production_hardware_evidence_status["production_ready"] = False
            production_hardware_evidence_status["status"] = "blocked"
            production_hardware_evidence_status.setdefault("gaps", []).append(production_hardware_evidence_error)
        wallet_authority["production_hardware_evidence"] = production_hardware_evidence_status
        wallet_authority["signer_ceremony"] = evaluate_perps_wallet_signer_ceremony_v1(
            wallet_authority_hash=None if wallet_authority_profile is None else wallet_authority_profile.get("wallet_authority_hash"),
            device_approval_status=wallet_authority.get("device_approval_exercise")
            if isinstance(wallet_authority.get("device_approval_exercise"), Mapping)
            else None,
            signer_device_status=wallet_authority.get("signer_device_integration")
            if isinstance(wallet_authority.get("signer_device_integration"), Mapping)
            else None,
            signer_prompt_capture_status=wallet_authority.get("signer_prompt_capture")
            if isinstance(wallet_authority.get("signer_prompt_capture"), Mapping)
            else None,
            signer_execution_status=wallet_authority.get("signer_execution_exercise")
            if isinstance(wallet_authority.get("signer_execution_exercise"), Mapping)
            else None,
        )
        wallet_authority["hardware_custody"] = evaluate_perps_wallet_hardware_custody_v1(
            wallet_authority_hash=None if wallet_authority_profile is None else wallet_authority_profile.get("wallet_authority_hash"),
            device_approval_status=wallet_authority.get("device_approval_exercise")
            if isinstance(wallet_authority.get("device_approval_exercise"), Mapping)
            else None,
            signer_device_status=wallet_authority.get("signer_device_integration")
            if isinstance(wallet_authority.get("signer_device_integration"), Mapping)
            else None,
            signer_prompt_capture_status=wallet_authority.get("signer_prompt_capture")
            if isinstance(wallet_authority.get("signer_prompt_capture"), Mapping)
            else None,
            signer_execution_status=wallet_authority.get("signer_execution_exercise")
            if isinstance(wallet_authority.get("signer_execution_exercise"), Mapping)
            else None,
            signer_ceremony_status=wallet_authority.get("signer_ceremony")
            if isinstance(wallet_authority.get("signer_ceremony"), Mapping)
            else None,
            production_hardware_evidence_status=production_hardware_evidence_status,
        )
    encrypted_sss_backup, encrypted_sss_backup_error = _wallet_encrypted_sss_backup_from_env()
    if encrypted_sss_backup is not None:
        recipient_root_keys, recipient_root_keys_error = _wallet_encrypted_sss_recipient_keys_from_env()
        wallet_authority["encrypted_sss_backup"] = evaluate_perps_wallet_encrypted_sss_backup_v1(
            wallet_authority_profile,
            encrypted_sss_backup,
            expected_chain_id=chain_id,
            recipient_root_keys=recipient_root_keys,
        )
        if recipient_root_keys_error is not None:
            wallet_authority["encrypted_sss_backup"]["ok"] = False
            wallet_authority["encrypted_sss_backup"]["encrypted_sss_backup_ready"] = False
            wallet_authority["encrypted_sss_backup"]["status"] = "blocked"
            wallet_authority["encrypted_sss_backup"].setdefault("errors", []).append(recipient_root_keys_error)
    elif encrypted_sss_backup_error is not None:
        wallet_authority["encrypted_sss_backup"] = {
            "schema": "zenodex/perps-wallet-encrypted-sss-backup-status/v1",
            "ok": False,
            "encrypted_sss_backup_ready": False,
            "status": "blocked",
            "errors": [encrypted_sss_backup_error],
            "wallet_authority_hash": None if wallet_authority_profile is None else wallet_authority_profile.get("wallet_authority_hash"),
            "backup_hash": None,
            "sss_implemented": True,
            "production_security_claim": False,
        }
    oracle_authority_profile, oracle_authority_error = _oracle_authority_profile_from_env()
    oracle_authority = _bind_oracle_authority_status(
        evaluate_oracle_authority_profile_v1(oracle_authority_profile),
        profile=oracle_authority_profile,
        profile_error=oracle_authority_error,
        expected_chain_id=chain_id,
    )
    status: Dict[str, Any] = {
        "enabled": True,
        "chain_id": chain_id,
        "tau_host": _env_str("PERPS_WALLET_TAU_HOST", _env_str("ZUSD_MONETARY_WALLET_TAU_HOST", "127.0.0.1")),
        "tau_port": _env_int(
            "PERPS_WALLET_TAU_PORT",
            _env_int("ZUSD_MONETARY_WALLET_TAU_PORT", 65432, lo=1, hi=65535),
            lo=1,
            hi=65535,
        ),
        "allow_local_signing": _allow_signing(),
        "auto_mine": _auto_mine(),
        "supported_actions": sorted(_ACTIONS),
        "supports_clearinghouse_np_v1": True,
        "quote_asset_default": derive_zusd_tau_asset_id(chain_id=chain_id),
        "operator_pubkey": os.environ.get("TAU_DEX_OPERATOR_PUBKEY") or os.environ.get("TAU_DEX_PERP_OPERATOR_PUBKEY") or None,
        "oracle_pubkey": os.environ.get("TAU_DEX_PERP_ORACLE_PUBKEY") or os.environ.get("TAU_DEX_ORACLE_PUBKEY") or None,
        "require_oracle_adapter_for_clearinghouse_settle_epoch": _env_bool(
            "TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH",
            True,
        ),
        "allow_isolated_markets": _env_bool("TAU_DEX_ALLOW_ISOLATED_PERPS", False),
        "require_oracle_adapter_for_isolated_partial_liquidate": _env_bool(
            "TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_ISOLATED_PARTIAL_LIQUIDATE",
            True,
        ),
        "proof_profile": _perps_proof_profile(),
        "wallet_authority": wallet_authority,
        "production_wallet_authority": wallet_authority["production_wallet_authority"],
        "oracle_authority": oracle_authority,
        "production_oracle_authority": oracle_authority["production_authority"],
    }
    try:
        client = _tau_client()
        hello = client.rpc("hello version=1").strip()
        app_state, app_hash = _load_app_state(client)
        markets = _market_summaries(app_state)
        status["node_reachable"] = True
        status["hello"] = hello
        status["app_hash"] = app_hash
        status["app_bridge_available"] = bool(app_state or app_hash)
        status["market_count"] = len(markets)
        status["markets"] = markets
        if account:
            status["account"] = account
            status["account_view"] = _account_perps_view(markets, account)
    except Exception as exc:
        status["node_reachable"] = False
        status["error"] = f"{type(exc).__name__}: {exc}"
    return status


def handle_perps_wallet_request(method: str, path: str, body: Optional[bytes]) -> ResponseT:
    parsed_path = urlsplit(path)
    segments = [segment for segment in parsed_path.path.split("/") if segment]
    if len(segments) < 4 or segments[0] != "api" or segments[1] != "perps" or segments[2] != "wallet":
        return 404, {"ok": False, "error": "not_found"}

    rest = segments[3:]
    try:
        if method == "GET" and rest == ["status"]:
            # Account-aware status: the connected wallet's positions/collateral are
            # resolved for the ?account=<pubkey> query (mirrors the pool surface).
            # Fail closed on a malformed account rather than silently dropping it.
            account_param = _query_first(parsed_path.query, "account")
            account: str | None = None
            if account_param:
                account = _canonical_pubkey(account_param, name="account")
            return 200, {"ok": True, "status": _status_payload(account)}
        if method != "POST":
            return 405, {"ok": False, "error": "method_not_allowed"}
        parsed, err = _parse_json_body(body)
        if err is not None:
            return 400, {"ok": False, "error": err}
        if parsed is None:
            return 400, {"ok": False, "error": "bad_json"}
        if rest == ["prepare"]:
            payload = _build_prepare_response(parsed, for_submit=False)
            return (200 if payload.get("ok") is True else 400), payload
        if rest == ["submit"]:
            # The local Tau writer exposes one mempool/sequence lane. Keep the
            # read-build-send-mine-postcheck cycle atomic for this API process.
            with _PERPS_TAU_WRITE_LOCK:
                payload = _build_prepare_response(parsed, for_submit=True)
            return (200 if payload.get("ok") is True else 400), payload
        if rest == ["testnet-faucet"]:
            # The local faucet is fixture-only and signs with one authority key.
            # Share the write lock with /submit so post-state balance checks
            # cannot race a collateral deposit or position update.
            with _PERPS_TAU_WRITE_LOCK:
                payload = _build_testnet_faucet_response(parsed)
            return (200 if payload.get("ok") is True else 400), payload
        if rest == ["oracle-bridge-template"]:
            action = str(parsed.get("action", "settle_epoch")).strip().lower()
            if action not in {"run_epoch", "settle_epoch", "partial_liquidate"}:
                return 400, {"ok": False, "error": "unsupported_oracle_bridge_action"}
            chain_id = str(parsed.get("chain_id") or _tau_chain_id())
            client = _tau_client()
            app_state, _app_hash = _load_app_state(client)
            config = _build_perp_config(chain_id=chain_id)
            account_pubkey: str | None = None
            fraction_bps = 0
            if action == "partial_liquidate":
                account_pubkey = _account_pubkey(parsed, field="account_pubkey", privkey_field="account_privkey")
                fraction_bps = _request_u32(parsed, name="fraction_bps")
                if fraction_bps > 10_000:
                    raise ValueError("bad_fraction_bps")
            return 200, _local_perps_oracle_bridge_fixture(
                app_state=app_state,
                config=config,
                market_id=_market_id(parsed, action=action),
                action=action,
                account_pubkey=account_pubkey,
                fraction_bps=fraction_bps,
            )
        if rest == ["oracle-bridge", "inspect"]:
            return 200, _inspect_oracle_adapter_bridge(parsed)
        if rest == ["recovery", "evaluate"]:
            chain_id = str(parsed.get("chain_id") or _tau_chain_id())
            profile, profile_error = _wallet_authority_profile_from_env()
            recovery = evaluate_perps_wallet_recovery_exercise_v1(
                profile,
                parsed,
                expected_chain_id=chain_id,
            )
            if profile_error is not None:
                recovery["ok"] = False
                recovery["recovery_exercise_ready"] = False
                recovery["status"] = "blocked"
                recovery.setdefault("errors", []).append(profile_error)
            return 200, {"ok": recovery.get("recovery_exercise_ready") is True, "recovery_exercise": recovery}
        if rest == ["rotation", "evaluate"]:
            chain_id = str(parsed.get("chain_id") or _tau_chain_id())
            profile, profile_error = _wallet_authority_profile_from_env()
            rotation = evaluate_perps_wallet_rotation_exercise_v1(
                profile,
                parsed,
                expected_chain_id=chain_id,
            )
            if profile_error is not None:
                rotation["ok"] = False
                rotation["rotation_exercise_ready"] = False
                rotation["status"] = "blocked"
                rotation.setdefault("errors", []).append(profile_error)
            return 200, {"ok": rotation.get("rotation_exercise_ready") is True, "rotation_exercise": rotation}
        if rest == ["device-approval", "evaluate"]:
            chain_id = str(parsed.get("chain_id") or _tau_chain_id())
            profile, profile_error = _wallet_authority_profile_from_env()
            device_approval = evaluate_perps_wallet_device_approval_exercise_v1(
                profile,
                parsed,
                expected_chain_id=chain_id,
            )
            if profile_error is not None:
                device_approval["ok"] = False
                device_approval["device_approval_ready"] = False
                device_approval["status"] = "blocked"
                device_approval.setdefault("errors", []).append(profile_error)
            return 200, {"ok": device_approval.get("device_approval_ready") is True, "device_approval_exercise": device_approval}
        if rest == ["signer-device", "evaluate"]:
            chain_id = str(parsed.get("chain_id") or _tau_chain_id())
            profile, profile_error = _wallet_authority_profile_from_env()
            signer_device = evaluate_perps_wallet_signer_device_integration_v1(
                profile,
                parsed,
                expected_chain_id=chain_id,
            )
            if profile_error is not None:
                signer_device["ok"] = False
                signer_device["signer_device_ready"] = False
                signer_device["status"] = "blocked"
                signer_device.setdefault("errors", []).append(profile_error)
            return 200, {"ok": signer_device.get("signer_device_ready") is True, "signer_device_integration": signer_device}
        if rest == ["signer-prompt-capture", "evaluate"]:
            chain_id = str(parsed.get("chain_id") or _tau_chain_id())
            profile, profile_error = _wallet_authority_profile_from_env()
            signer_prompt_capture = evaluate_perps_wallet_signer_prompt_capture_v1(
                profile,
                parsed,
                expected_chain_id=chain_id,
            )
            if profile_error is not None:
                signer_prompt_capture["ok"] = False
                signer_prompt_capture["signer_prompt_capture_ready"] = False
                signer_prompt_capture["status"] = "blocked"
                signer_prompt_capture.setdefault("errors", []).append(profile_error)
            return 200, {
                "ok": signer_prompt_capture.get("signer_prompt_capture_ready") is True,
                "signer_prompt_capture": signer_prompt_capture,
            }
        if rest == ["signer-execution", "evaluate"]:
            chain_id = str(parsed.get("chain_id") or _tau_chain_id())
            profile, profile_error = _wallet_authority_profile_from_env()
            signer_execution = evaluate_perps_wallet_signer_execution_exercise_v1(
                profile,
                parsed,
                expected_chain_id=chain_id,
            )
            if profile_error is not None:
                signer_execution["ok"] = False
                signer_execution["signer_execution_ready"] = False
                signer_execution["status"] = "blocked"
                signer_execution.setdefault("errors", []).append(profile_error)
            return 200, {"ok": signer_execution.get("signer_execution_ready") is True, "signer_execution_exercise": signer_execution}
        if rest == ["signer-ceremony", "evaluate"]:
            chain_id = str(parsed.get("chain_id") or _tau_chain_id())
            profile, profile_error = _wallet_authority_profile_from_env()
            device_approval_status = evaluate_perps_wallet_device_approval_exercise_v1(
                profile,
                parsed.get("device_approval_exercise") if isinstance(parsed.get("device_approval_exercise"), Mapping) else None,
                expected_chain_id=chain_id,
            )
            signer_device_status = evaluate_perps_wallet_signer_device_integration_v1(
                profile,
                parsed.get("signer_device_integration") if isinstance(parsed.get("signer_device_integration"), Mapping) else None,
                expected_chain_id=chain_id,
            )
            signer_prompt_capture_status = evaluate_perps_wallet_signer_prompt_capture_v1(
                profile,
                parsed.get("signer_prompt_capture") if isinstance(parsed.get("signer_prompt_capture"), Mapping) else None,
                expected_chain_id=chain_id,
            )
            signer_execution_status = evaluate_perps_wallet_signer_execution_exercise_v1(
                profile,
                parsed.get("signer_execution_exercise") if isinstance(parsed.get("signer_execution_exercise"), Mapping) else None,
                expected_chain_id=chain_id,
            )
            signer_ceremony = evaluate_perps_wallet_signer_ceremony_v1(
                wallet_authority_hash=None if profile is None else profile.get("wallet_authority_hash"),
                device_approval_status=device_approval_status,
                signer_device_status=signer_device_status,
                signer_prompt_capture_status=signer_prompt_capture_status,
                signer_execution_status=signer_execution_status,
            )
            if profile_error is not None:
                signer_ceremony["ok"] = False
                signer_ceremony["signer_ceremony_ready"] = False
                signer_ceremony["status"] = "blocked"
                signer_ceremony.setdefault("errors", []).append(profile_error)
            return 200, {"ok": signer_ceremony.get("signer_ceremony_ready") is True, "signer_ceremony": signer_ceremony}
        if rest == ["hardware-custody", "evaluate"]:
            chain_id = str(parsed.get("chain_id") or _tau_chain_id())
            profile, profile_error = _wallet_authority_profile_from_env()
            device_approval_status = evaluate_perps_wallet_device_approval_exercise_v1(
                profile,
                parsed.get("device_approval_exercise") if isinstance(parsed.get("device_approval_exercise"), Mapping) else None,
                expected_chain_id=chain_id,
            )
            signer_device_status = evaluate_perps_wallet_signer_device_integration_v1(
                profile,
                parsed.get("signer_device_integration") if isinstance(parsed.get("signer_device_integration"), Mapping) else None,
                expected_chain_id=chain_id,
            )
            signer_prompt_capture_status = evaluate_perps_wallet_signer_prompt_capture_v1(
                profile,
                parsed.get("signer_prompt_capture") if isinstance(parsed.get("signer_prompt_capture"), Mapping) else None,
                expected_chain_id=chain_id,
            )
            signer_execution_status = evaluate_perps_wallet_signer_execution_exercise_v1(
                profile,
                parsed.get("signer_execution_exercise") if isinstance(parsed.get("signer_execution_exercise"), Mapping) else None,
                expected_chain_id=chain_id,
            )
            signer_ceremony = evaluate_perps_wallet_signer_ceremony_v1(
                wallet_authority_hash=None if profile is None else profile.get("wallet_authority_hash"),
                device_approval_status=device_approval_status,
                signer_device_status=signer_device_status,
                signer_prompt_capture_status=signer_prompt_capture_status,
                signer_execution_status=signer_execution_status,
            )
            production_hardware_evidence_status = evaluate_production_hardware_wallet_evidence_v1(
                parsed.get("production_hardware_evidence")
                if isinstance(parsed.get("production_hardware_evidence"), Mapping)
                else None,
                wallet_authority_profile_hash=None if profile is None else profile.get("wallet_authority_hash"),
                expected_device_pubkey=None,
            )
            hardware_custody = evaluate_perps_wallet_hardware_custody_v1(
                wallet_authority_hash=None if profile is None else profile.get("wallet_authority_hash"),
                device_approval_status=device_approval_status,
                signer_device_status=signer_device_status,
                signer_prompt_capture_status=signer_prompt_capture_status,
                signer_execution_status=signer_execution_status,
                signer_ceremony_status=signer_ceremony,
                production_hardware_evidence_status=production_hardware_evidence_status,
            )
            hardware_custody["production_hardware_evidence"] = production_hardware_evidence_status
            if profile_error is not None:
                hardware_custody["ok"] = False
                hardware_custody["hardware_custody_ready"] = False
                hardware_custody["status"] = "blocked"
                hardware_custody.setdefault("errors", []).append(profile_error)
            return 200, {"ok": hardware_custody.get("hardware_custody_ready") is True, "hardware_custody": hardware_custody}
        if rest == ["encrypted-sss-backup", "evaluate"]:
            chain_id = str(parsed.get("chain_id") or _tau_chain_id())
            profile, profile_error = _wallet_authority_profile_from_env()
            recipient_root_keys, recipient_root_keys_error = _wallet_encrypted_sss_recipient_keys_from_env()
            encrypted_sss_backup = evaluate_perps_wallet_encrypted_sss_backup_v1(
                profile,
                parsed,
                expected_chain_id=chain_id,
                recipient_root_keys=recipient_root_keys,
            )
            if profile_error is not None:
                encrypted_sss_backup["ok"] = False
                encrypted_sss_backup["encrypted_sss_backup_ready"] = False
                encrypted_sss_backup["status"] = "blocked"
                encrypted_sss_backup.setdefault("errors", []).append(profile_error)
            if recipient_root_keys_error is not None:
                encrypted_sss_backup["ok"] = False
                encrypted_sss_backup["encrypted_sss_backup_ready"] = False
                encrypted_sss_backup["status"] = "blocked"
                encrypted_sss_backup.setdefault("errors", []).append(recipient_root_keys_error)
            return 200, {
                "ok": encrypted_sss_backup.get("encrypted_sss_backup_ready") is True,
                "encrypted_sss_backup": encrypted_sss_backup,
            }
        if rest == ["encrypted-sss-backup", "deliver"]:
            payload = _build_encrypted_sss_provider_delivery_response(parsed)
            return (200 if payload.get("ok") is True else 400), payload
        return 404, {"ok": False, "error": "not_found"}
    except (ValueError, TypeError) as exc:
        return 400, {"ok": False, "error": str(exc)}
    except TauNetRpcError as exc:
        return 502, {"ok": False, "error": "tau_rpc_error", "detail": str(exc)}
