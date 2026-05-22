from __future__ import annotations

import hashlib
import json
from pathlib import Path

from src.integration.zenograph_ranking_review_bundle_verify import (
    verify_zenograph_ranking_review_bundle_manifest,
)


def test_verify_zenograph_ranking_review_bundle_manifest_detects_tamper(
    tmp_path: Path,
) -> None:
    artifact = tmp_path / "artifact.txt"
    artifact.write_text("hello\n", encoding="utf-8")
    manifest = {
        "schema": "zenodex/zenograph-autotrader-ranking-review-bundle/v1",
        "bundle_dir": str(tmp_path),
        "artifacts": {
            "summary": {
                "path": str(artifact),
                "bytes": len(artifact.read_bytes()),
                "sha256": hashlib.sha256(artifact.read_bytes()).hexdigest(),
            }
        },
    }
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True), encoding="utf-8")

    ok_result = verify_zenograph_ranking_review_bundle_manifest(
        manifest_path=manifest_path,
        payload=manifest,
    )
    assert ok_result.ok is True

    artifact.write_text("tampered\n", encoding="utf-8")
    bad_result = verify_zenograph_ranking_review_bundle_manifest(
        manifest_path=manifest_path,
        payload=manifest,
    )
    assert bad_result.ok is False
    assert bad_result.sha256_mismatches == ("summary",)
