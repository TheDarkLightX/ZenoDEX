from __future__ import annotations

import json
import tempfile
from functools import lru_cache
from pathlib import Path

from tools.build_shape_v1_release_bundle import build_shape_v1_release_bundle
from tools.check_shape_v1_ratchet import check_shape_v1_ratchet
from tools.check_shape_v1_release_bundle import (
    main,
    verify_shape_v1_release_bundle_payload,
)


@lru_cache(maxsize=1)
def _bundle_path() -> Path:
    base = Path(tempfile.mkdtemp(prefix="shape-v1-release-bundle-check-"))
    ratchet_report = base / "shape-v1-ratchet.json"
    bridge_report = base / "cantor-bridge.json"
    bundle_path = base / "shape-v1-release-bundle.json"
    check_shape_v1_ratchet(
        cantor_bridge_report_path=bridge_report,
        output_report_path=ratchet_report,
    )
    bundle = build_shape_v1_release_bundle(
        ratchet_report_path=ratchet_report,
        cantor_bridge_report_path=bridge_report,
    )
    bundle_path.write_text(json.dumps(bundle, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return bundle_path


def test_verify_shape_v1_release_bundle_accepts_current_bundle() -> None:
    payload = json.loads(_bundle_path().read_text(encoding="utf-8"))
    ok, err = verify_shape_v1_release_bundle_payload(payload, require_current=True)
    assert ok, err


def test_verify_shape_v1_release_bundle_rejects_tampered_digest() -> None:
    payload = json.loads(_bundle_path().read_text(encoding="utf-8"))
    payload["artifact_sha256"] = dict(payload["artifact_sha256"])
    payload["artifact_sha256"]["world_model"] = "0" * 64
    ok, err = verify_shape_v1_release_bundle_payload(payload)
    assert not ok
    assert err == "bundle world_model sha256 does not match file content"


def test_check_shape_v1_release_bundle_cli_accepts_current_bundle() -> None:
    assert main([str(_bundle_path()), "--require-current"]) == 0


def test_check_shape_v1_release_bundle_cli_rejects_tampered_bundle(tmp_path: Path) -> None:
    payload = json.loads(_bundle_path().read_text(encoding="utf-8"))
    payload["cantor_bridge_report"] = dict(payload["cantor_bridge_report"])
    payload["cantor_bridge_report"]["mapped_surface_count"] = 999
    bundle_path = tmp_path / "bad-bundle.json"
    bundle_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    assert main([str(bundle_path)]) == 1
