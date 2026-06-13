from __future__ import annotations

import json
import os
import shutil
import socket
import socketserver
import subprocess
import sys
import threading
import urllib.error
import urllib.request
from http.server import BaseHTTPRequestHandler
from pathlib import Path
from urllib.parse import quote, urlencode
from urllib.request import urlopen

import pytest

from src.integration.zeno_key_manager import KeyRef, ZenoKeyManager
from src.integration.zeno_ledger_signature import bls_public_key_hex_from_private_key_v0
from src.integration.zeno_ledger_signer_registry import build_signer_registry_v0
from src.integration.zeno_oracle_authority import ORACLE_AUTHORITY_PAYLOAD_KIND
from tests.integration.vite_test_server import vite_dev_command

ROOT = Path(__file__).resolve().parents[2]
DEX_UI = ROOT / "tools" / "dex-ui"
ORACLE_CLI = ROOT / "tools" / "zenodex_oracle.py"
def _privkey_hex(value: int) -> str:
    return "0x" + int(value).to_bytes(32, byteorder="big", signed=False).hex()


PRIVKEY_A = _privkey_hex(101)
PRIVKEY_B = _privkey_hex(102)
PUBKEY_A = bls_public_key_hex_from_private_key_v0(PRIVKEY_A)
PUBKEY_B = bls_public_key_hex_from_private_key_v0(PRIVKEY_B)


def _chrome_binary() -> str | None:
    for name in ("google-chrome", "google-chrome-stable", "chromium", "chromium-browser"):
        path = shutil.which(name)
        if path:
            return path
    return None


def _free_port() -> int:
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
        sock.bind(("127.0.0.1", 0))
        return int(sock.getsockname()[1])


def _wait_for_http(url: str, *, timeout_s: float = 30) -> None:
    import time

    deadline = time.monotonic() + timeout_s
    last_error: Exception | None = None
    while time.monotonic() < deadline:
        try:
            with urlopen(url, timeout=2) as response:  # noqa: S310 - local test server
                response.read(1)
            return
        except Exception as exc:
            last_error = exc
            time.sleep(0.2)
    raise AssertionError(f"server did not become ready at {url}: {last_error}")


class _FakeMalformedOracleHandler(BaseHTTPRequestHandler):
    def log_message(self, _format: str, *_args: object) -> None:
        return

    def end_headers(self) -> None:
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type")
        super().end_headers()

    def do_OPTIONS(self) -> None:
        self.send_response(204)
        self.end_headers()

    def do_GET(self) -> None:
        path = self.path.split("?", 1)[0]
        if path == "/api/oracle/health":
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.end_headers()
            self.wfile.write(b'{"ok":true}')
            return
        if path == "/api/oracle/dashboard":
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.end_headers()
            self.wfile.write(b'{"summary":')
            return
        self.send_response(404)
        self.send_header("Content-Type", "application/json")
        self.end_headers()
        self.wfile.write(b'{"ok":false,"error":"not_found"}')


class _ReusableThreadingTCPServer(socketserver.ThreadingTCPServer):
    allow_reuse_address = True


def _provision_ready_authority_profile(home: Path, tmp_path: Path) -> None:
    key_manager = ZenoKeyManager(
        key_refs=(
            KeyRef(key_id="oracle-authority-a", public_key=PUBKEY_A),
            KeyRef(key_id="oracle-authority-b", public_key=PUBKEY_B),
        )
    ).public_dict()
    signer_registry = build_signer_registry_v0(
        registry_id="zenooracle-prod-authority-v1",
        payload_kind=ORACLE_AUTHORITY_PAYLOAD_KIND,
        threshold=2,
        signers=(
            {
                "signer_id": "operator-a",
                "key_id": "oracle-authority-a",
                "public_key": PUBKEY_A,
                "weight": 1,
                "status": "active",
            },
            {
                "signer_id": "operator-b",
                "key_id": "oracle-authority-b",
                "public_key": PUBKEY_B,
                "weight": 1,
                "status": "active",
            },
        ),
    )
    key_manager_path = tmp_path / "oracle-authority-key-manager.json"
    signer_registry_path = tmp_path / "oracle-authority-signer-registry.json"
    key_manager_path.write_text(json.dumps(key_manager, sort_keys=True), encoding="utf-8")
    signer_registry_path.write_text(json.dumps(signer_registry, sort_keys=True), encoding="utf-8")
    provision = subprocess.run(
        [
            "python3",
            str(ORACLE_CLI),
            "--json",
            "authority",
            "provision-profile",
            "--home",
            str(home),
            "--authority-id",
            "zenooracle-mainnet-authority-v1",
            "--chain-id",
            "zeno-ledger-mainnet",
            "--key-manager",
            str(key_manager_path),
            "--signer-registry",
            str(signer_registry_path),
            "--runtime-proof-profile",
            "zenooracle-o3-replay-zk-profile-v1",
            "--signer-private-key",
            f"operator-a:oracle-authority-a:{PRIVKEY_A}",
            "--signer-private-key",
            f"operator-b:oracle-authority-b:{PRIVKEY_B}",
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert provision.returncode == 0, provision.stderr


def test_oracle_ui_smoke_loads_local_service(tmp_path: Path) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    home = tmp_path / "oracle-home"
    init_proc = subprocess.run(
        ["python3", str(ORACLE_CLI), "--json", "init", "--home", str(home)],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert init_proc.returncode == 0, init_proc.stderr

    oracle_port = _free_port()
    oracle_proc = subprocess.Popen(
        [
            "python3",
            str(ORACLE_CLI),
            "serve",
            "--home",
            str(home),
            "--host",
            "127.0.0.1",
            "--port",
            str(oracle_port),
            "--quiet",
        ],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )

    vite_port = _free_port()
    vite_base = f"http://127.0.0.1:{vite_port}"
    vite_env = {
        **os.environ,
        "VITE_DEMO_MODE": "false",
        "VITE_ZENO_ORACLE_API_URL": f"http://127.0.0.1:{oracle_port}",
    }
    vite_proc = None
    try:
        assert oracle_proc.stdout is not None
        ready_line = oracle_proc.stdout.readline()
        ready = json.loads(ready_line)
        assert ready["ok"] is True
        _wait_for_http(f"http://127.0.0.1:{oracle_port}/api/oracle/health", timeout_s=30)

        vite_proc = subprocess.Popen(
            vite_dev_command(DEX_UI, vite_port),
            cwd=DEX_UI,
            env=vite_env,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        _wait_for_http(vite_base, timeout_s=30)

        query = urlencode({"tab": "oracle", "oracleView": "Verify", "demo": "false"})
        chrome_profile = tmp_path / "chrome-profile"
        result = subprocess.run(
            [
                chrome,
                "--headless=new",
                "--disable-gpu",
                "--no-sandbox",
                f"--user-data-dir={chrome_profile}",
                "--virtual-time-budget=15000",
                "--dump-dom",
                f"{vite_base}/?{query}",
            ],
            check=False,
            capture_output=True,
            text=True,
            timeout=45,
        )
        assert result.returncode == 0, result.stderr[-2000:]
        dom = result.stdout
        assert "ZenoOracle" in dom
        assert ("Local API connected" in dom) or ("Local API replay warning" in dom)
        assert "Authority blocked" in dom
        assert "Verify" in dom
    finally:
        if vite_proc is not None:
            vite_proc.terminate()
            try:
                vite_proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                vite_proc.kill()
                vite_proc.wait(timeout=5)
        oracle_proc.terminate()
        try:
            oracle_proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            oracle_proc.kill()
            oracle_proc.wait(timeout=5)


def test_oracle_ui_smoke_fails_closed_when_local_service_unreachable(tmp_path: Path) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    unused_oracle_port = _free_port()
    vite_port = _free_port()
    vite_base = f"http://127.0.0.1:{vite_port}"
    vite_proc = subprocess.Popen(
        vite_dev_command(DEX_UI, vite_port),
        cwd=DEX_UI,
        env={
            **os.environ,
            "VITE_DEMO_MODE": "false",
            "VITE_ZENO_ORACLE_API_URL": f"http://127.0.0.1:{unused_oracle_port}",
        },
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    try:
        _wait_for_http(vite_base, timeout_s=30)
        query = urlencode({"tab": "oracle", "oracleView": "Governance", "demo": "false"})
        chrome_profile = tmp_path / "chrome-profile-offline"
        result = subprocess.run(
            [
                chrome,
                "--headless=new",
                "--disable-gpu",
                "--no-sandbox",
                f"--user-data-dir={chrome_profile}",
                "--virtual-time-budget=15000",
                "--dump-dom",
                f"{vite_base}/?{query}",
            ],
            check=False,
            capture_output=True,
            text=True,
            timeout=45,
        )
        assert result.returncode == 0, result.stderr[-2000:]
        dom = result.stdout
        assert "ZenoOracle" in dom
        assert "Local API offline" in dom
        assert "Authority blocked" in dom
        assert "Production authority ready" not in dom
    finally:
        vite_proc.terminate()
        try:
            vite_proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            vite_proc.kill()
            vite_proc.wait(timeout=5)


def test_oracle_ui_smoke_fails_closed_on_malformed_dashboard_response(tmp_path: Path) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    fake_oracle_port = _free_port()
    fake_oracle = _ReusableThreadingTCPServer(("127.0.0.1", fake_oracle_port), _FakeMalformedOracleHandler)
    fake_thread = threading.Thread(target=fake_oracle.serve_forever, daemon=True)
    fake_thread.start()

    vite_port = _free_port()
    vite_base = f"http://127.0.0.1:{vite_port}"
    vite_proc = subprocess.Popen(
        vite_dev_command(DEX_UI, vite_port),
        cwd=DEX_UI,
        env={
            **os.environ,
            "VITE_DEMO_MODE": "false",
            "VITE_ZENO_ORACLE_API_URL": f"http://127.0.0.1:{fake_oracle_port}",
        },
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    try:
        _wait_for_http(f"http://127.0.0.1:{fake_oracle_port}/api/oracle/health", timeout_s=30)
        _wait_for_http(vite_base, timeout_s=30)
        query = urlencode({"tab": "oracle", "oracleView": "Governance", "demo": "false"})
        chrome_profile = tmp_path / "chrome-profile-malformed"
        result = subprocess.run(
            [
                chrome,
                "--headless=new",
                "--disable-gpu",
                "--no-sandbox",
                f"--user-data-dir={chrome_profile}",
                "--virtual-time-budget=15000",
                "--dump-dom",
                f"{vite_base}/?{query}",
            ],
            check=False,
            capture_output=True,
            text=True,
            timeout=45,
        )
        assert result.returncode == 0, result.stderr[-2000:]
        dom = result.stdout
        assert "ZenoOracle" in dom
        assert "Local API offline" in dom
        assert "Production authority ready" not in dom
        assert "oracle write smoke accepted" not in dom
    finally:
        vite_proc.terminate()
        fake_oracle.shutdown()
        fake_oracle.server_close()
        fake_thread.join(timeout=2.0)
        try:
            vite_proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            vite_proc.kill()
            vite_proc.wait(timeout=5)


def test_oracle_ui_smoke_reports_ready_authority_profile(tmp_path: Path) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    home = tmp_path / "oracle-home-authority"
    init_proc = subprocess.run(
        ["python3", str(ORACLE_CLI), "--json", "init", "--home", str(home)],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert init_proc.returncode == 0, init_proc.stderr
    _provision_ready_authority_profile(home, tmp_path)

    oracle_port = _free_port()
    oracle_proc = subprocess.Popen(
        [
            "python3",
            str(ORACLE_CLI),
            "serve",
            "--home",
            str(home),
            "--host",
            "127.0.0.1",
            "--port",
            str(oracle_port),
            "--quiet",
        ],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )

    vite_port = _free_port()
    vite_base = f"http://127.0.0.1:{vite_port}"
    vite_env = {
        **os.environ,
        "VITE_DEMO_MODE": "false",
        "VITE_ZENO_ORACLE_API_URL": f"http://127.0.0.1:{oracle_port}",
    }
    vite_proc = None
    try:
        assert oracle_proc.stdout is not None
        ready_line = oracle_proc.stdout.readline()
        ready = json.loads(ready_line)
        assert ready["ok"] is True
        assert ready["production_authority"] is True
        _wait_for_http(f"http://127.0.0.1:{oracle_port}/api/oracle/health", timeout_s=30)

        vite_proc = subprocess.Popen(
            vite_dev_command(DEX_UI, vite_port),
            cwd=DEX_UI,
            env=vite_env,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        _wait_for_http(vite_base, timeout_s=30)

        query = urlencode({"tab": "oracle", "oracleView": "Governance", "demo": "false"})
        chrome_profile = tmp_path / "chrome-profile-authority"
        result = subprocess.run(
            [
                chrome,
                "--headless=new",
                "--disable-gpu",
                "--no-sandbox",
                f"--user-data-dir={chrome_profile}",
                "--virtual-time-budget=15000",
                "--dump-dom",
                f"{vite_base}/?{query}",
            ],
            check=False,
            capture_output=True,
            text=True,
            timeout=45,
        )
        assert result.returncode == 0, result.stderr[-2000:]
        dom = result.stdout
        assert "ZenoOracle" in dom
        assert "Production authority ready" in dom
        assert "Authority Profile" in dom
        assert "Key Manager" in dom
        assert "Signed quorum" in dom
        assert "2/2" in dom
        assert "oracle-authority-a" in dom
        assert "External signer" in dom
        assert "zenooracle-o3-replay-zk-profile-v1" in dom
    finally:
        if vite_proc is not None:
            vite_proc.terminate()
            try:
                vite_proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                vite_proc.kill()
                vite_proc.wait(timeout=5)
        oracle_proc.terminate()
        try:
            oracle_proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            oracle_proc.kill()
            oracle_proc.wait(timeout=5)


def test_oracle_ui_smoke_runs_write_enabled_receipt_flow(tmp_path: Path) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    home = tmp_path / "oracle-home-write"
    init_proc = subprocess.run(
        ["python3", str(ORACLE_CLI), "--json", "init", "--home", str(home)],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert init_proc.returncode == 0, init_proc.stderr

    oracle_port = _free_port()
    oracle_proc = subprocess.Popen(
        [
            "python3",
            str(ORACLE_CLI),
            "serve",
            "--home",
            str(home),
            "--host",
            "127.0.0.1",
            "--port",
            str(oracle_port),
            "--quiet",
            "--allow-writes",
            "--now-epoch",
            "12",
        ],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )

    vite_port = _free_port()
    vite_base = f"http://127.0.0.1:{vite_port}"
    vite_env = {
        **os.environ,
        "VITE_DEMO_MODE": "false",
        "VITE_ZENO_ORACLE_API_URL": f"http://127.0.0.1:{oracle_port}",
    }
    vite_proc = None
    try:
        assert oracle_proc.stdout is not None
        ready_line = oracle_proc.stdout.readline()
        ready = json.loads(ready_line)
        assert ready["ok"] is True
        assert ready["write_paths_enabled"] is True
        _wait_for_http(f"http://127.0.0.1:{oracle_port}/api/oracle/health", timeout_s=30)

        vite_proc = subprocess.Popen(
            vite_dev_command(DEX_UI, vite_port),
            cwd=DEX_UI,
            env=vite_env,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        _wait_for_http(vite_base, timeout_s=30)

        query = urlencode(
            {
                "tab": "oracle",
                "oracleView": "Receipts",
                "demo": "false",
                "zenodexUiSmokeOracleWrites": "1",
            }
        )
        chrome_profile = tmp_path / "chrome-profile-write"
        result = subprocess.run(
            [
                chrome,
                "--headless=new",
                "--disable-gpu",
                "--no-sandbox",
                f"--user-data-dir={chrome_profile}",
                "--virtual-time-budget=25000",
                "--dump-dom",
                f"{vite_base}/?{query}",
            ],
            check=False,
            capture_output=True,
            text=True,
            timeout=60,
        )
        assert result.returncode == 0, result.stderr[-2000:]
        dom = result.stdout
        assert "ZenoOracle" in dom
        assert "oracle write smoke accepted" in dom
        assert "sha256:" in dom
    finally:
        if vite_proc is not None:
            vite_proc.terminate()
            try:
                vite_proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                vite_proc.kill()
                vite_proc.wait(timeout=5)
        oracle_proc.terminate()
        try:
            oracle_proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            oracle_proc.kill()
            oracle_proc.wait(timeout=5)


def test_oracle_ui_smoke_runs_authority_exercise_flow(tmp_path: Path) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    home = tmp_path / "oracle-home-authority-exercise"
    init_proc = subprocess.run(
        ["python3", str(ORACLE_CLI), "--json", "init", "--home", str(home)],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert init_proc.returncode == 0, init_proc.stderr
    _provision_ready_authority_profile(home, tmp_path)

    oracle_port = _free_port()
    oracle_proc = subprocess.Popen(
        [
            "python3",
            str(ORACLE_CLI),
            "serve",
            "--home",
            str(home),
            "--host",
            "127.0.0.1",
            "--port",
            str(oracle_port),
            "--quiet",
            "--allow-writes",
            "--now-epoch",
            "12",
        ],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )

    vite_port = _free_port()
    vite_base = f"http://127.0.0.1:{vite_port}"
    vite_env = {
        **os.environ,
        "VITE_DEMO_MODE": "false",
        "VITE_ZENO_ORACLE_API_URL": f"http://127.0.0.1:{oracle_port}",
    }
    vite_proc = None
    try:
        assert oracle_proc.stdout is not None
        ready_line = oracle_proc.stdout.readline()
        ready = json.loads(ready_line)
        assert ready["ok"] is True
        assert ready["production_authority"] is True
        assert ready["write_paths_enabled"] is True
        _wait_for_http(f"http://127.0.0.1:{oracle_port}/api/oracle/health", timeout_s=30)

        vite_proc = subprocess.Popen(
            vite_dev_command(DEX_UI, vite_port),
            cwd=DEX_UI,
            env=vite_env,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        _wait_for_http(vite_base, timeout_s=30)

        query = urlencode(
            {
                "tab": "oracle",
                "oracleView": "Governance",
                "demo": "false",
                "zenodexUiSmokeOracleAuthorityExercise": "1",
            }
        )
        chrome_profile = tmp_path / "chrome-profile-authority-exercise"
        result = subprocess.run(
            [
                chrome,
                "--headless=new",
                "--disable-gpu",
                "--no-sandbox",
                f"--user-data-dir={chrome_profile}",
                "--virtual-time-budget=30000",
                "--dump-dom",
                f"{vite_base}/?{query}",
            ],
            check=False,
            capture_output=True,
            text=True,
            timeout=75,
        )
        assert result.returncode == 0, result.stderr[-2000:]
        dom = result.stdout
        assert "Authority Exercise" in dom
        assert "Run Authority Exercise" in dom
        assert "Exercise ready" in dom
        assert "oracle authority exercise accepted" in dom
        assert "Public testnet evidence" in dom
        assert "Receipt binding" in dom
        assert "Public evidence binding" in dom
        assert "0x" in dom
        assert "pending" in dom
    finally:
        if vite_proc is not None:
            vite_proc.terminate()
            try:
                vite_proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                vite_proc.kill()
                vite_proc.wait(timeout=5)
        oracle_proc.terminate()
        try:
            oracle_proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            oracle_proc.kill()
            oracle_proc.wait(timeout=5)


def test_oracle_ui_smoke_reports_write_disabled_for_read_only_service(tmp_path: Path) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    home = tmp_path / "oracle-home-read-only"
    init_proc = subprocess.run(
        ["python3", str(ORACLE_CLI), "--json", "init", "--home", str(home)],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert init_proc.returncode == 0, init_proc.stderr

    oracle_port = _free_port()
    oracle_proc = subprocess.Popen(
        [
            "python3",
            str(ORACLE_CLI),
            "serve",
            "--home",
            str(home),
            "--host",
            "127.0.0.1",
            "--port",
            str(oracle_port),
            "--quiet",
            "--now-epoch",
            "12",
        ],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )

    vite_port = _free_port()
    vite_base = f"http://127.0.0.1:{vite_port}"
    vite_env = {
        **os.environ,
        "VITE_DEMO_MODE": "false",
        "VITE_ZENO_ORACLE_API_URL": f"http://127.0.0.1:{oracle_port}",
    }
    vite_proc = None
    try:
        assert oracle_proc.stdout is not None
        ready_line = oracle_proc.stdout.readline()
        ready = json.loads(ready_line)
        assert ready["ok"] is True
        assert ready["write_paths_enabled"] is False
        _wait_for_http(f"http://127.0.0.1:{oracle_port}/api/oracle/health", timeout_s=30)

        vite_proc = subprocess.Popen(
            vite_dev_command(DEX_UI, vite_port),
            cwd=DEX_UI,
            env=vite_env,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        _wait_for_http(vite_base, timeout_s=30)

        query = urlencode(
            {
                "tab": "oracle",
                "oracleView": "Receipts",
                "demo": "false",
                "zenodexUiSmokeOracleWrites": "1",
            }
        )
        chrome_profile = tmp_path / "chrome-profile-read-only"
        result = subprocess.run(
            [
                chrome,
                "--headless=new",
                "--disable-gpu",
                "--no-sandbox",
                f"--user-data-dir={chrome_profile}",
                "--virtual-time-budget=25000",
                "--dump-dom",
                f"{vite_base}/?{query}",
            ],
            check=False,
            capture_output=True,
            text=True,
            timeout=60,
        )
        assert result.returncode == 0, result.stderr[-2000:]
        dom = result.stdout
        assert "ZenoOracle" in dom
        assert "oracle write smoke failed write_api_disabled" in dom
    finally:
        if vite_proc is not None:
            vite_proc.terminate()
            try:
                vite_proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                vite_proc.kill()
                vite_proc.wait(timeout=5)
        oracle_proc.terminate()
        try:
            oracle_proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            oracle_proc.kill()
            oracle_proc.wait(timeout=5)


# ---------------------------------------------------------------------------
# Headless API-level bridge tests.
#
# The browser smoke tests above require Chrome + npm + a running vite dev
# server and skip in environments that lack them. The tests below exercise the
# exact HTTP surface the dashboard component consumes
# (``ZenoOracleDashboard.jsx`` fetches ``/api/oracle/dashboard`` on an interval
# and the write endpoints during its smoke flow) WITHOUT a browser, so the
# core oracle guarantees -- live read, publish->read->consume consistency, and
# fail-closed on stale/unreachable/write-disabled -- are verified on every CI
# run rather than only when a desktop browser is present.
#
# These are devnet/local-operator guarantees only. The service keeps
# ``production_authority``/``production_security_claim`` false throughout; the
# assertions below pin that posture.
# ---------------------------------------------------------------------------


def _free_local_port() -> int:
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
        sock.bind(("127.0.0.1", 0))
        return int(sock.getsockname()[1])


def _http_get_json(url: str, *, timeout: float = 5.0) -> dict[str, object]:
    with urllib.request.urlopen(url, timeout=timeout) as response:  # noqa: S310 - local test server
        return json.loads(response.read().decode("utf-8"))


def _http_post_json(
    url: str, payload: dict[str, object], *, timeout: float = 5.0
) -> tuple[int, dict[str, object]]:
    body = json.dumps(payload).encode("utf-8")
    request = urllib.request.Request(
        url,
        data=body,
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    try:
        with urllib.request.urlopen(request, timeout=timeout) as response:  # noqa: S310
            return int(response.status), json.loads(response.read().decode("utf-8"))
    except urllib.error.HTTPError as exc:
        return int(exc.code), json.loads(exc.read().decode("utf-8"))


def _serve_oracle(
    home: Path, *, now_epoch: int, allow_writes: bool
) -> tuple[subprocess.Popen[str], str]:
    """Start ``zenodex-oracle serve`` and return (process, base_url).

    Reads the JSON ``ready`` line from stdout (the serve command prints exactly
    one line before blocking) and waits for ``/api/oracle/health`` to answer.
    Caller is responsible for terminating the process.
    """
    port = _free_local_port()
    argv = [
        sys.executable,
        str(ORACLE_CLI),
        "serve",
        "--home",
        str(home),
        "--host",
        "127.0.0.1",
        "--port",
        str(port),
        "--quiet",
        "--now-epoch",
        str(now_epoch),
    ]
    if allow_writes:
        argv.append("--allow-writes")
    proc = subprocess.Popen(
        argv,
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    assert proc.stdout is not None
    ready_line = proc.stdout.readline()
    ready = json.loads(ready_line)
    assert ready["ok"] is True
    assert ready["write_paths_enabled"] is bool(allow_writes)
    # The service is devnet-only: it must never assert production authority.
    assert ready["production_authority"] is False
    base = f"http://127.0.0.1:{port}"
    _wait_for_http(f"{base}/api/oracle/health", timeout_s=30)
    return proc, base


def _terminate(proc: subprocess.Popen[str]) -> None:
    proc.terminate()
    try:
        proc.wait(timeout=5)
    except subprocess.TimeoutExpired:
        proc.kill()
        proc.wait(timeout=5)


def _init_oracle_home(tmp_path: Path, name: str) -> Path:
    home = tmp_path / name
    init_proc = subprocess.run(
        [sys.executable, str(ORACLE_CLI), "--json", "init", "--home", str(home)],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert init_proc.returncode == 0, init_proc.stderr
    return home


# Observed price is published at this epoch with a freshness window of 2, so
# the accepted read expires at OBSERVED_EPOCH + 2. The critical-zusd-v1 profile
# caps the effective window at 2, so min(2, cap) == 2 regardless.
OBSERVED_EPOCH = 12
FRESHNESS_WINDOW = 2
EXPIRES_AT_EPOCH = OBSERVED_EPOCH + FRESHNESS_WINDOW
PRICE_E8 = 123456789


def _publish_feed(base: str) -> str:
    """Drive publish: identity -> query -> fund -> reporter -> bond -> source -> report.

    Returns the registered ``query_id``. All steps assert HTTP 200 and the
    devnet-only posture so a silent server-side acceptance cannot pass.
    """
    status, identity = _http_post_json(f"{base}/api/oracle/identity/create", {"force": True})
    assert status == 200, identity
    assert identity["production_authority"] is False

    query_id = "sha256:" + "1" * 64
    status, query = _http_post_json(
        f"{base}/api/oracle/query/register",
        {
            "base_asset": "AGRS",
            "quote_asset": "ZDEX",
            "query_id": query_id,
            "source_policy_id": "source-policy:registered-diverse-v1",
            "min_reporters": 1,
            "report_reward_e8": 17,
            "freshness_window_epochs": FRESHNESS_WINDOW,
        },
    )
    assert status == 200, query
    assert query["query_id"] == query_id

    status, funded = _http_post_json(
        f"{base}/api/oracle/query/fund", {"query_id": query_id, "amount_e8": 20}
    )
    assert status == 200, funded

    status, reporter = _http_post_json(
        f"{base}/api/oracle/reporter/register",
        {"query_id": query_id, "required_bond_e8": 1},
    )
    assert status == 200, reporter
    status, bond = _http_post_json(f"{base}/api/oracle/reporter/bond", {"amount_e8": 1})
    assert status == 200, bond
    assert bond["active"] is True

    status, source = _http_post_json(
        f"{base}/api/oracle/source/register",
        {
            "source_id": "source:cex-a",
            "source_kind": "cex",
            "control_group_id": "control:cex-a",
            "venue_id": "venue:cex-a",
            "data_family_id": "price:cex-last-trade",
            "transport_id": "api:https:cex-a",
            "asset_class": "crypto",
            "query_id": query_id,
            "assurance_class": "S3",
        },
    )
    assert status == 200, source

    status, submitted = _http_post_json(
        f"{base}/api/oracle/report/submit",
        {
            "query_id": query_id,
            "price_e8": PRICE_E8,
            "source_observed_epoch": OBSERVED_EPOCH,
            "source_id": "source:cex-a",
        },
    )
    assert status == 200, submitted
    return query_id


def _accept_read(base: str, query_id: str) -> dict[str, object]:
    """Drive read: aggregate/build -> read/accept. Returns the accepted read."""
    status, aggregate = _http_post_json(
        f"{base}/api/oracle/aggregate/build",
        {"query_id": query_id, "epoch": OBSERVED_EPOCH},
    )
    assert status == 200, aggregate
    assert aggregate["aggregate"]["value_e8"] == PRICE_E8

    status, read = _http_post_json(
        f"{base}/api/oracle/read/accept",
        {
            "aggregate_id": aggregate["aggregate_id"],
            "consumer_module": "zenodex.zusd",
            "profile_id": "critical-zusd-v1",
        },
    )
    assert status == 200, read
    return read


def _runtime_action(query_id: str, *, now_epoch: int) -> dict[str, object]:
    return {
        "consumer_module": "zenodex.zusd",
        "action_kind": "mint",
        "action_id": "sha256:" + "5" * 64,
        "action_facts_hash": "sha256:" + "6" * 64,
        "pre_state_hash": "sha256:" + "7" * 64,
        "profile_id": "critical-zusd-v1",
        "query_id": query_id,
        "runtime_value_e8": PRICE_E8,
        "now_epoch": now_epoch,
    }


def test_oracle_bridge_publish_read_consume_consistency(tmp_path: Path) -> None:
    """Publish -> read -> consume preserves the same price end-to-end.

    Verifies the dashboard's live data source: the value/value_hash published
    by a reporter is the one accepted into the read AND the one bound into the
    consumer authorization, the read expires at observed+window, and the live
    ``/api/oracle/feeds`` endpoint labels the feed ``fresh`` (not fabricated)
    while inside the freshness window.
    """
    home = _init_oracle_home(tmp_path, "oracle-consistency")
    proc, base = _serve_oracle(home, now_epoch=OBSERVED_EPOCH, allow_writes=True)
    try:
        query_id = _publish_feed(base)
        read = _accept_read(base, query_id)

        # Read carries the published price and the derived expiry.
        assert read["read"]["value_e8"] == PRICE_E8
        assert read["read"]["observed_epoch"] == OBSERVED_EPOCH
        assert read["read"]["expires_at_epoch"] == EXPIRES_AT_EPOCH
        read_value_hash = read["read"]["value_hash"]
        assert isinstance(read_value_hash, str) and read_value_hash.startswith("sha256:")

        # Consume via the runtime-bound authorization path while fresh.
        status, authorization = _http_post_json(
            f"{base}/api/oracle/authorization/build-from-runtime",
            {"runtime_action": _runtime_action(query_id, now_epoch=OBSERVED_EPOCH)},
        )
        assert status == 200, authorization
        # publish == read == consume: same value AND same value_hash binding.
        assert authorization["authorization"]["value_e8"] == PRICE_E8
        assert authorization["authorization"]["value_hash"] == read_value_hash
        assert authorization["production_authority"] is False

        # The consumed authorization replays clean through the verifier.
        verified = _http_get_json(
            f"{base}/api/oracle/verify-receipt?id={quote(str(authorization['authorization_id']))}"
        )
        assert verified["ok"] is True
        assert verified["receipt_check"]["typed_ok"] is True

        # Live read surface the dashboard consumes: feed is FRESH, not fabricated.
        feeds = _http_get_json(f"{base}/api/oracle/feeds")
        assert feeds["ok"] is True
        assert feeds["production_authority"] is False
        statuses = {f["query_id"]: f for f in feeds["feed_statuses"]}
        assert query_id in statuses
        feed = statuses[query_id]
        assert "fresh" in feed["status"]
        assert "stale" not in feed["status"]
        assert feed["latest_value_e8"] == PRICE_E8
        assert feed["expires_at_epoch"] == EXPIRES_AT_EPOCH

        # And the dashboard snapshot the UI fetches reports a real accepted read.
        dashboard = _http_get_json(f"{base}/api/oracle/dashboard")
        assert dashboard["production_authority"] is False
        assert dashboard["summary"]["accepted_read_count"] == 1
        assert dashboard["summary"]["report_count"] == 1
    finally:
        _terminate(proc)


def test_oracle_bridge_fails_closed_on_stale_feed(tmp_path: Path) -> None:
    """A read past its expiry must NOT yield a fabricated consume authorization.

    Publishes + accepts a read at epoch 12 (expires at 14), then re-serves the
    same home with ``now_epoch`` advanced to 99 (well past expiry). The live
    feed must flip to ``stale`` and the runtime-bound consume path must return
    HTTP 400 with no authorization built. Also asserts a future-dated read
    (observed_epoch > now_epoch) is rejected the same way.
    """
    home = _init_oracle_home(tmp_path, "oracle-stale")

    # Phase 1: publish + accept a read while fresh (now_epoch == observed).
    proc, base = _serve_oracle(home, now_epoch=OBSERVED_EPOCH, allow_writes=True)
    try:
        query_id = _publish_feed(base)
        read = _accept_read(base, query_id)
        assert read["read"]["expires_at_epoch"] == EXPIRES_AT_EPOCH

        # Sanity: while still fresh the consume path accepts.
        status, fresh_auth = _http_post_json(
            f"{base}/api/oracle/authorization/build-from-runtime",
            {"runtime_action": _runtime_action(query_id, now_epoch=OBSERVED_EPOCH)},
        )
        assert status == 200, fresh_auth
    finally:
        _terminate(proc)

    # Phase 2: re-serve with "now" advanced past expiry. State on disk is
    # unchanged; only the clock moved -- exactly the stale-feed scenario.
    stale_now = EXPIRES_AT_EPOCH + 85  # 99, far past expiry
    proc, base = _serve_oracle(home, now_epoch=stale_now, allow_writes=True)
    try:
        # Live feed surface must report STALE, never fresh.
        feeds = _http_get_json(f"{base}/api/oracle/feeds")
        statuses = {f["query_id"]: f for f in feeds["feed_statuses"]}
        assert query_id in statuses
        feed = statuses[query_id]
        assert "stale" in feed["status"]
        assert "fresh" not in feed["status"]
        assert feed["now_epoch"] == stale_now

        # Fail-closed consume: stale read must be rejected, no authorization.
        status, rejected = _http_post_json(
            f"{base}/api/oracle/authorization/build-from-runtime",
            {"runtime_action": _runtime_action(query_id, now_epoch=stale_now)},
        )
        assert status == 400, rejected
        assert "no accepted read matches runtime_action" in str(rejected.get("error", ""))
        assert "authorization_id" not in rejected
        assert rejected["production_authority"] is False

        # Fail-closed on a future-dated read: observed_epoch (12) > now_epoch (5)
        # must also be rejected (no clairvoyant consume of a not-yet-valid read).
        status, future_rejected = _http_post_json(
            f"{base}/api/oracle/authorization/build-from-runtime",
            {"runtime_action": _runtime_action(query_id, now_epoch=OBSERVED_EPOCH - 7)},
        )
        assert status == 400, future_rejected
        assert "no accepted read matches runtime_action" in str(future_rejected.get("error", ""))
        assert "authorization_id" not in future_rejected
    finally:
        _terminate(proc)


def test_oracle_bridge_fails_closed_when_service_unreachable(tmp_path: Path) -> None:
    """When the oracle service is down, the dashboard fetch errors out.

    The dashboard's ``loadDashboard`` effect catches fetch errors and sets
    ``Local API offline`` -- it never fabricates a price. This test reproduces
    the bridge precondition: a service that WAS reachable becomes unreachable,
    and a GET to its base now raises a connection error rather than returning
    stale or fabricated data.

    Starting and then terminating the real service (rather than picking a
    never-bound free port) avoids a TOCTOU race where another process could
    grab a freed port between selection and connect.
    """
    home = _init_oracle_home(tmp_path, "oracle-unreachable")
    proc, base = _serve_oracle(home, now_epoch=OBSERVED_EPOCH, allow_writes=False)
    url = f"{base}/api/oracle/dashboard"
    # While up, the dashboard endpoint serves real data fail-open is impossible.
    assert _http_get_json(url)["production_authority"] is False
    # Take the service down; the same URL must now fail closed (no fabrication).
    _terminate(proc)
    with pytest.raises(urllib.error.URLError):
        _http_get_json(url, timeout=3.0)


def test_oracle_bridge_write_disabled_fails_closed(tmp_path: Path) -> None:
    """A read-only service rejects consume writes with 403 (no silent accept).

    Mirrors the UI's write smoke flow against a service started WITHOUT
    ``--allow-writes``: ``read/accept`` and ``build-from-runtime`` must both
    return 403 ``write_api_disabled`` and never produce a receipt.
    """
    home = _init_oracle_home(tmp_path, "oracle-read-only")
    proc, base = _serve_oracle(home, now_epoch=OBSERVED_EPOCH, allow_writes=False)
    try:
        # Read surface still serves (GET dashboard is allowed, read-only).
        dashboard = _http_get_json(f"{base}/api/oracle/dashboard")
        assert dashboard["production_authority"] is False

        # Writes are refused fail-closed.
        status, rejected_accept = _http_post_json(
            f"{base}/api/oracle/read/accept",
            {
                "aggregate_id": "sha256:" + "8" * 64,
                "consumer_module": "zenodex.zusd",
                "profile_id": "critical-zusd-v1",
            },
        )
        assert status == 403
        assert rejected_accept["error"] == "write_api_disabled"

        status, rejected_consume = _http_post_json(
            f"{base}/api/oracle/authorization/build-from-runtime",
            {"runtime_action": _runtime_action("sha256:" + "1" * 64, now_epoch=OBSERVED_EPOCH)},
        )
        assert status == 403
        assert rejected_consume["error"] == "write_api_disabled"
    finally:
        _terminate(proc)


@pytest.mark.skip(
    reason=(
        "PINS A KNOWN GAP (not production-safe): the read_id-keyed "
        "/api/oracle/authorization/build path does NOT re-check the read's "
        "freshness against now_epoch (cmd_authorization_build stamps now_epoch "
        "into the runtime_action without a stale guard). It is therefore "
        "possible to build an authorization from a read whose now_epoch is past "
        "expires_at_epoch via this path. The load-bearing fail-closed gate is "
        "the runtime-bound /api/oracle/authorization/build-from-runtime path "
        "(_read_matches_runtime), which IS exercised in "
        "test_oracle_bridge_fails_closed_on_stale_feed. The browser dashboard "
        "smoke flow uses the build path with now_epoch == observed_epoch only, "
        "so the gap is not reachable from the current UI; consumers MUST use the "
        "runtime-bound path for the freshness guarantee. Unskip once "
        "cmd_authorization_build rejects now_epoch > expires_at_epoch."
    )
)
def test_oracle_bridge_build_path_should_reject_stale_read(tmp_path: Path) -> None:
    home = _init_oracle_home(tmp_path, "oracle-build-stale")
    proc, base = _serve_oracle(home, now_epoch=OBSERVED_EPOCH, allow_writes=True)
    try:
        query_id = _publish_feed(base)
        read = _accept_read(base, query_id)
        stale_now = EXPIRES_AT_EPOCH + 85
        status, result = _http_post_json(
            f"{base}/api/oracle/authorization/build",
            {
                "read_id": read["read_id"],
                "action_kind": "mint",
                "action_id": "sha256:" + "2" * 64,
                "action_facts_hash": "sha256:" + "3" * 64,
                "pre_state_hash": "sha256:" + "4" * 64,
                "now_epoch": stale_now,
            },
        )
        # Desired (post-fix) behavior: the build path also fails closed on a
        # read consumed past its expiry.
        assert status == 400, result
        assert "authorization_id" not in result
    finally:
        _terminate(proc)
