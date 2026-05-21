from __future__ import annotations

import json
import os
import shutil
import socket
import socketserver
import subprocess
import threading
from http.server import BaseHTTPRequestHandler
from pathlib import Path
from urllib.parse import urlencode
from urllib.request import urlopen

import pytest

from src.integration.zeno_key_manager import KeyRef, ZenoKeyManager
from src.integration.zeno_ledger_signature import bls_public_key_hex_from_private_key_v0
from src.integration.zeno_ledger_signer_registry import build_signer_registry_v0
from src.integration.zeno_oracle_authority import ORACLE_AUTHORITY_PAYLOAD_KIND


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
            ["npm", "run", "dev", "--", "--host", "127.0.0.1", "--port", str(vite_port)],
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
        ["npm", "run", "dev", "--", "--host", "127.0.0.1", "--port", str(vite_port)],
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
        ["npm", "run", "dev", "--", "--host", "127.0.0.1", "--port", str(vite_port)],
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
            ["npm", "run", "dev", "--", "--host", "127.0.0.1", "--port", str(vite_port)],
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
            ["npm", "run", "dev", "--", "--host", "127.0.0.1", "--port", str(vite_port)],
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
            ["npm", "run", "dev", "--", "--host", "127.0.0.1", "--port", str(vite_port)],
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
            ["npm", "run", "dev", "--", "--host", "127.0.0.1", "--port", str(vite_port)],
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
