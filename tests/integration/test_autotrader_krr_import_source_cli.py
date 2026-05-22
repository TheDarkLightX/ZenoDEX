from __future__ import annotations

import http.server
import json
import socket
import subprocess
import sys
import threading
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
CLI_PATH = REPO_ROOT / "tools" / "autotrader_krr_import_source.py"


class _SourceHandler(http.server.BaseHTTPRequestHandler):
    body = b""

    def do_GET(self) -> None:  # noqa: N802
        self.send_response(200)
        self.send_header("Content-Type", "text/plain")
        self.send_header("Content-Length", str(len(self.body)))
        self.end_headers()
        self.wfile.write(self.body)

    def log_message(self, format: str, *args: object) -> None:  # noqa: A003
        _ = format, args


def _free_port() -> int:
    with socket.socket() as sock:
        sock.bind(("127.0.0.1", 0))
        return int(sock.getsockname()[1])


def test_autotrader_krr_import_source_cli_local_file_roundtrip(tmp_path: Path) -> None:
    source_path = tmp_path / "research_note.txt"
    source_path.write_text("Macro spread widened 12bps.\n", encoding="utf-8")
    snapshot_path = tmp_path / "snapshot.json"
    body_path = tmp_path / "body.bin"
    text_path = tmp_path / "decoded.txt"
    evidence_path = tmp_path / "evidence.json"

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--source-id",
            "research.note.alpha",
            "--source-class",
            "research_paper",
            "--source-uri",
            str(source_path),
            "--title",
            "Research Note",
            "--license",
            "CC-BY-4.0",
            "--snapshot-out",
            str(snapshot_path),
            "--body-out",
            str(body_path),
            "--text-out",
            str(text_path),
            "--evidence-out",
            str(evidence_path),
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["ok"] is True
    assert report["text_decoded"] is True
    assert snapshot_path.exists()
    assert body_path.read_bytes() == source_path.read_bytes()
    assert text_path.read_text(encoding="utf-8") == source_path.read_text(encoding="utf-8")
    snapshot = json.loads(snapshot_path.read_text(encoding="utf-8"))
    evidence = json.loads(evidence_path.read_text(encoding="utf-8"))
    assert snapshot["schema"] == "zenodex/krr-source-snapshot/v1"
    assert evidence["schema"] == "zenodex/krr-evidence-record/v1"
    assert evidence["snapshot_id"] == snapshot["snapshot_id"]


def test_autotrader_krr_import_source_cli_rejects_insecure_http_without_flag(tmp_path: Path) -> None:
    snapshot_path = tmp_path / "snapshot.json"
    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--source-id",
            "feed.bad.http",
            "--source-class",
            "news",
            "--source-uri",
            "http://example.com/feed.json",
            "--snapshot-out",
            str(snapshot_path),
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 1
    report = json.loads(proc.stderr)
    assert report["ok"] is False
    assert "plain http is not allowed" in report["error"]


def test_autotrader_krr_import_source_cli_rejects_oversized_remote_body(tmp_path: Path) -> None:
    _SourceHandler.body = b"x" * 16
    server = http.server.ThreadingHTTPServer(("127.0.0.1", _free_port()), _SourceHandler)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        proc = subprocess.run(
            [
                sys.executable,
                str(CLI_PATH),
                "--source-id",
                "feed.too.large",
                "--source-class",
                "news",
                "--source-uri",
                f"http://127.0.0.1:{server.server_port}/source.txt",
                "--allow-insecure-http",
                "--max-bytes",
                "8",
                "--snapshot-out",
                str(tmp_path / "snapshot.json"),
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
    assert "exceeds max_bytes" in report["error"]
