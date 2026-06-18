from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import yaml

from tools import rc1_readiness


def test_build_status_payload_contract_uses_manifest_and_checks_routes(tmp_path: Path) -> None:
    root = tmp_path
    (root / "tools").mkdir()
    (root / "docs").mkdir()
    (root / "src" / "integration").mkdir(parents=True)

    manifest = {
        "schema": "zenodex/rc1-scope-manifest/v1",
        "required_docs": ["docs/RC1_READINESS.md"],
        "required_files": ["tools/prod_gate.sh", "src/integration/api_server.py"],
        "supported_http_boundary": {
            "file": "src/integration/api_server.py",
            "routes": ["/health", "/api/dex/quote"],
        },
        "excluded_claims_expected_disputed": ["claim:one", "claim:two"],
        "supported_commands": [["python3", "tools/permissionless_assurance.py", "status"]],
        "excluded_experimental_surfaces": ["tools/autotrader_live.py"],
    }
    (root / "tools" / "rc1_scope_manifest.json").write_text(json.dumps(manifest), encoding="utf-8")
    (root / "docs" / "claims_registry.yaml").write_text(
        yaml.safe_dump(
            {
                "claims": [
                    {"id": "claim:one", "status": "disputed"},
                    {"id": "claim:two", "status": "supported"},
                ]
            }
        ),
        encoding="utf-8",
    )
    (root / "docs" / "RC1_READINESS.md").write_text("# rc1\n", encoding="utf-8")
    (root / "tools" / "prod_gate.sh").write_text("#!/usr/bin/env bash\n", encoding="utf-8")
    (root / "src" / "integration" / "api_server.py").write_text(
        'if path == "/health": pass\nif path == "/api/dex/quote": pass\n',
        encoding="utf-8",
    )

    payload = rc1_readiness._build_status_payload(
        root=root,
        manifest=manifest,
        assurance_payload={
            "assurance_snapshot": {"ok": True, "error": None},
            "tla_claim_summary": {"ok": True, "error": None},
            "lanes": [{"name": "release", "ready": True}],
            "dirty_count": 0,
            "branch": "test",
        },
        claim_statuses={"claim:one": "disputed", "claim:two": "supported"},
    )

    assert payload["checks"]["scope_docs_present"] is True
    assert payload["checks"]["supported_http_routes_present"] is True
    assert payload["checks"]["excluded_claims_still_disputed"] is False
    assert payload["checks"]["release_lane_files_present"] is True
    assert "excluded_claims_still_disputed" in payload["unmet_criteria"]
    assert payload["supported_http_boundary"]["missing_routes"] == []


def test_route_presence_follows_dex_dispatch_registry_files(tmp_path: Path) -> None:
    root = tmp_path
    (root / "src" / "integration").mkdir(parents=True)
    (root / "src" / "integration" / "api_server.py").write_text('if path == "/health": pass\n', encoding="utf-8")
    (root / "src" / "integration" / "dex_dispatch_handlers.py").write_text(
        '_register("/api/dex/verify_quote_receipt", _handle_verify_quote_receipt)\n',
        encoding="utf-8",
    )
    (root / "src" / "integration" / "dex_dispatch_settlement_end_to_end_certificate_handlers.py").write_text(
        '_register("/api/dex/build_settlement_end_to_end_certificate_packet", _handle_build)\n',
        encoding="utf-8",
    )

    presence = rc1_readiness._route_presence(
        root,
        "src/integration/api_server.py",
        [
            "/health",
            "/api/dex/verify_quote_receipt",
            "/api/dex/build_settlement_end_to_end_certificate_packet",
            "/api/dex/missing",
        ],
    )

    assert presence == {
        "/health": True,
        "/api/dex/verify_quote_receipt": True,
        "/api/dex/build_settlement_end_to_end_certificate_packet": True,
        "/api/dex/missing": False,
    }


def test_rc1_readiness_cli_json_shape() -> None:
    root = Path(__file__).resolve().parents[2]
    proc = subprocess.run(
        [sys.executable, "tools/rc1_readiness.py", "--format", "json"],
        cwd=root,
        check=True,
        capture_output=True,
        text=True,
    )
    payload = json.loads(proc.stdout)

    assert payload["schema"] == "zenodex/rc1-readiness-status/v1"
    assert "overall_ok" in payload
    assert "checks" in payload
    assert "supported_http_boundary" in payload
    assert payload["checks"]["supported_runtime_path_ok"] is True
    assert payload["checks"]["tau_supported_runtime_subset_ok"] is True
    assert payload["checks"]["verified_surface_matrix_ok"] is True
    assert isinstance(payload["checks"]["assurance_snapshot_ok"], bool)
    assert isinstance(payload["checks"]["tla_claim_summary_ok"], bool)
