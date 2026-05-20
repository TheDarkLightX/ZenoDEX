from __future__ import annotations

import http.server
import json
import socket
import subprocess
import sys
import threading
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
CLI_PATH = REPO_ROOT / "tools" / "autotrader_krr_import_wikidata.py"


class _Handler(http.server.BaseHTTPRequestHandler):
    entity_payload: dict[str, object] = {}
    dump_body: bytes = b""
    include_dump_content_length = True

    def do_GET(self) -> None:  # noqa: N802
        if self.path == "/wikidatawiki/entities/latest-all.json.bz2":
            self.send_response(200)
            self.send_header("Content-Type", "application/x-bzip2")
            if self.include_dump_content_length:
                self.send_header("Content-Length", str(len(self.dump_body)))
            self.end_headers()
            self.wfile.write(self.dump_body)
            return
        if self.path != "/wiki/Special:EntityData/Q312.json":
            self.send_response(404)
            self.end_headers()
            return
        body = json.dumps(self.entity_payload, sort_keys=True).encode("utf-8")
        self.send_response(200)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_HEAD(self) -> None:  # noqa: N802
        if self.path != "/wikidatawiki/entities/latest-all.json.bz2":
            self.send_response(404)
            self.end_headers()
            return
        self.send_response(200)
        self.send_header("Content-Type", "application/x-bzip2")
        if self.include_dump_content_length:
            self.send_header("Content-Length", str(len(self.dump_body)))
        self.end_headers()

    def log_message(self, format: str, *args: object) -> None:  # noqa: A003
        _ = format, args


def _free_port() -> int:
    with socket.socket() as sock:
        sock.bind(("127.0.0.1", 0))
        return int(sock.getsockname()[1])


def test_autotrader_krr_import_wikidata_cli_financial_trading_profile(tmp_path: Path) -> None:
    _Handler.entity_payload = {
        "entities": {
            "Q312": {
                "id": "Q312",
                "type": "item",
                "lastrevid": 123456789,
                "modified": "2026-03-12T00:00:00Z",
                "labels": {
                    "en": {"language": "en", "value": "Apple Inc."},
                },
                "descriptions": {
                    "en": {"language": "en", "value": "American technology company"},
                },
                "claims": {
                    "P1278": [
                        {
                            "id": "Q312$lei",
                            "rank": "normal",
                            "mainsnak": {
                                "snaktype": "value",
                                "datavalue": {"type": "string", "value": "HWUPKR0MPOU8FGXBT394"},
                            },
                        }
                    ],
                    "P946": [
                        {
                            "id": "Q312$isin",
                            "rank": "normal",
                            "mainsnak": {
                                "snaktype": "value",
                                "datavalue": {"type": "string", "value": "US0378331005"},
                            },
                        }
                    ],
                    "P414": [
                        {
                            "id": "Q312$nasdaq_preferred",
                            "rank": "preferred",
                            "mainsnak": {
                                "snaktype": "value",
                                "datavalue": {
                                    "type": "wikibase-entityid",
                                    "value": {"entity-type": "item", "id": "Q82059", "numeric-id": 82059},
                                },
                            },
                        },
                        {
                            "id": "Q312$deprecated_exchange",
                            "rank": "deprecated",
                            "mainsnak": {
                                "snaktype": "value",
                                "datavalue": {
                                    "type": "wikibase-entityid",
                                    "value": {"entity-type": "item", "id": "Q13677", "numeric-id": 13677},
                                },
                            },
                        },
                    ],
                    "P452": [
                        {
                            "id": "Q312$industry",
                            "rank": "normal",
                            "mainsnak": {
                                "snaktype": "value",
                                "datavalue": {
                                    "type": "wikibase-entityid",
                                    "value": {"entity-type": "item", "id": "Q11661", "numeric-id": 11661},
                                },
                            },
                        }
                    ],
                },
            }
        }
    }

    server = http.server.ThreadingHTTPServer(("127.0.0.1", _free_port()), _Handler)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        out_dir = tmp_path / "wikidata_out"
        manifest_path = tmp_path / "manifest.json"
        proc = subprocess.run(
            [
                sys.executable,
                str(CLI_PATH),
                "--mode",
                "entity",
                "--entity-id",
                "Q312",
                "--profile",
                "financial-trading-reference",
                "--entity-base-url",
                f"http://127.0.0.1:{server.server_port}/wiki/Special:EntityData",
                "--allow-insecure-http",
                "--out-dir",
                str(out_dir),
                "--manifest-out",
                str(manifest_path),
                "--pretty",
            ],
            cwd=str(REPO_ROOT),
            check=False,
            capture_output=True,
            text=True,
        )
    finally:
        server.shutdown()
        server.server_close()
        thread.join(timeout=5.0)

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["ok"] is True
    assert report["profile"] == "financial-trading-reference"
    assert report["entity_count"] == 1
    entity_row = report["entities"][0]
    assert entity_row["claim_count"] >= 6
    assert entity_row["extra_evidence_paths"]

    claims_dir = out_dir / "canonical_claims"
    claims = [
        json.loads(path.read_text(encoding="utf-8"))
        for path in sorted(claims_dir.glob("*.json"))
    ]
    claim_keys = {(row["fact_family"], row["attribute_key"], row["value"]) for row in claims}
    assert ("entity_identifier", "lei", "HWUPKR0MPOU8FGXBT394") in claim_keys
    assert ("instrument_identifier", "isin", "US0378331005") in claim_keys
    assert ("listing_reference", "stock_exchange", "Q82059") in claim_keys
    assert ("issuer_reference", "industry", "Q11661") in claim_keys

    stock_exchange_claims = [
        row for row in claims if row["attribute_key"] == "stock_exchange"
    ]
    assert len(stock_exchange_claims) == 1


def test_autotrader_krr_import_wikidata_cli_rejects_oversized_entity_response(tmp_path: Path) -> None:
    _Handler.entity_payload = {"entities": {"Q312": {"id": "Q312", "padding": "x" * 128}}}

    server = http.server.ThreadingHTTPServer(("127.0.0.1", _free_port()), _Handler)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        proc = subprocess.run(
            [
                sys.executable,
                str(CLI_PATH),
                "--mode",
                "entity",
                "--entity-id",
                "Q312",
                "--entity-base-url",
                f"http://127.0.0.1:{server.server_port}/wiki/Special:EntityData",
                "--allow-insecure-http",
                "--entity-max-bytes",
                "16",
                "--out-dir",
                str(tmp_path / "wikidata_out"),
            ],
            cwd=str(REPO_ROOT),
            check=False,
            capture_output=True,
            text=True,
        )
    finally:
        server.shutdown()
        server.server_close()
        thread.join(timeout=5.0)

    assert proc.returncode == 1
    report = json.loads(proc.stderr)
    assert report["ok"] is False
    assert "exceeds max_response_bytes" in report["error"]


def test_autotrader_krr_import_wikidata_cli_rejects_unbounded_dump_without_length(tmp_path: Path) -> None:
    _Handler.dump_body = b"x" * 32
    _Handler.include_dump_content_length = False

    server = http.server.ThreadingHTTPServer(("127.0.0.1", _free_port()), _Handler)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    dump_path = tmp_path / "dump.bz2"
    try:
        proc = subprocess.run(
            [
                sys.executable,
                str(CLI_PATH),
                "--mode",
                "dump-download",
                "--dump-base-url",
                f"http://127.0.0.1:{server.server_port}/wikidatawiki/entities",
                "--allow-insecure-http",
                "--dump-out",
                str(dump_path),
            ],
            cwd=str(REPO_ROOT),
            check=False,
            capture_output=True,
            text=True,
        )
    finally:
        server.shutdown()
        server.server_close()
        thread.join(timeout=5.0)
        _Handler.include_dump_content_length = True

    assert proc.returncode == 1
    report = json.loads(proc.stderr)
    assert report["ok"] is False
    assert "missing content-length" in report["error"]
    assert not dump_path.exists()


def test_autotrader_krr_import_wikidata_cli_rejects_oversized_dump_without_partial_file(tmp_path: Path) -> None:
    _Handler.dump_body = b"x" * 32
    _Handler.include_dump_content_length = False

    server = http.server.ThreadingHTTPServer(("127.0.0.1", _free_port()), _Handler)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    dump_path = tmp_path / "dump.bz2"
    try:
        proc = subprocess.run(
            [
                sys.executable,
                str(CLI_PATH),
                "--mode",
                "dump-download",
                "--dump-base-url",
                f"http://127.0.0.1:{server.server_port}/wikidatawiki/entities",
                "--allow-insecure-http",
                "--max-bytes",
                "16",
                "--chunk-bytes",
                "8",
                "--dump-out",
                str(dump_path),
            ],
            cwd=str(REPO_ROOT),
            check=False,
            capture_output=True,
            text=True,
        )
    finally:
        server.shutdown()
        server.server_close()
        thread.join(timeout=5.0)
        _Handler.include_dump_content_length = True

    assert proc.returncode == 1
    report = json.loads(proc.stderr)
    assert report["ok"] is False
    assert "exceeds --max-bytes" in report["error"]
    assert not dump_path.exists()
