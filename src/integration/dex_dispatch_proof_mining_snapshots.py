"""Writer snapshot loading helpers for proof-mining payout templates."""

from __future__ import annotations

import json
import os
import urllib as urllib
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path
from typing import Any, Mapping


def _load_latest_writer_snapshot_from_url_for_template(url: str) -> Mapping[str, Any]:
    url_text = str(url).strip()
    parsed = urllib.parse.urlparse(url_text)
    if parsed.scheme not in {"http", "https"} or not parsed.netloc:
        raise ValueError("writer snapshot URL must be absolute http or https")
    req = urllib.request.Request(url_text, headers={"Accept": "application/json"})
    # URL scheme and host are validated above.
    with urllib.request.urlopen(req, timeout=2.0) as resp:  # nosec B310
        payload = json.loads(resp.read().decode("utf-8"))
    if not isinstance(payload, Mapping) or payload.get("ok") is not True:
        raise ValueError("writer snapshot endpoint returned non-ok payload")
    snapshot_obj = payload.get("snapshot")
    if not isinstance(snapshot_obj, Mapping):
        raise ValueError("writer snapshot endpoint missing snapshot object")
    return snapshot_obj


def _load_latest_writer_snapshot_from_file_for_template(data_dir_raw: Any) -> Mapping[str, Any]:
    data_dir = Path(str(data_dir_raw)).resolve()
    live_state_path = data_dir / "live_state.json"
    live_state = json.loads(live_state_path.read_text(encoding="utf-8"))
    if not isinstance(live_state, Mapping):
        raise ValueError("live_state.json must decode to an object")
    rel = live_state.get("latest_snapshot_path")
    if not isinstance(rel, str) or not rel:
        raise ValueError("live_state.latest_snapshot_path missing")
    snapshot_path = Path(rel)
    if not snapshot_path.is_absolute():
        snapshot_path = data_dir / snapshot_path
    snapshot_path = snapshot_path.resolve()
    try:
        snapshot_path.relative_to(data_dir)
    except ValueError as exc:
        raise ValueError("live_state.latest_snapshot_path escapes writer data dir") from exc
    snapshot_obj = json.loads(snapshot_path.read_text(encoding="utf-8"))
    if not isinstance(snapshot_obj, Mapping):
        raise ValueError("latest snapshot must decode to an object")
    if snapshot_obj.get("schema") == "zenodex/tau_app_state/v1":
        dex_state = snapshot_obj.get("dex_state")
        if not isinstance(dex_state, Mapping):
            raise ValueError("tau app state dex_state must be an object")
        return dex_state
    return snapshot_obj


def _load_latest_writer_snapshot_for_template(ctx: Any) -> Mapping[str, Any]:
    data_dir_raw = getattr(ctx.server, "local_testnet_writer_data_dir", None)
    if data_dir_raw is not None:
        return _load_latest_writer_snapshot_from_file_for_template(data_dir_raw)

    snapshot_url = os.environ.get(
        "ZENO_LEDGER_WRITER_SNAPSHOT_URL",
        "http://zeno-ledger-writer:8787/api/dex/snapshot",
    ).strip()
    if snapshot_url:
        try:
            return _load_latest_writer_snapshot_from_url_for_template(snapshot_url)
        except (OSError, ValueError, urllib.error.URLError, TimeoutError, json.JSONDecodeError):
            pass

    data_dir_raw = os.environ.get("ZENO_LEDGER_WRITER_DATA_DIR", "/app/data/local-testnet/node-writer")
    return _load_latest_writer_snapshot_from_file_for_template(data_dir_raw)
