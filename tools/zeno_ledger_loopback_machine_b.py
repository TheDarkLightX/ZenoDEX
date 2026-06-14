#!/usr/bin/env python3
"""Run a Docker-isolated Machine B against a host Machine A.

This is a local fallback for the physical two-machine ZenoLedger public-testnet
rehearsal. It validates the public config URL, peer discovery, live pull, write
forwarding, and two-machine evidence archive path from a separate network
namespace when Wi-Fi, hotspot, or router policy blocks a second laptop.
"""

from __future__ import annotations

import argparse
import json
import os
import secrets
import shlex
import shutil
import socket
import subprocess
import sys
import tempfile
import textwrap
import time
from http import HTTPStatus
from pathlib import Path
from typing import Any
from urllib.request import Request, urlopen

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.zeno_ledger_make_testnet_bundle import (  # noqa: E402
    DEFAULT_ASSET0,
    DEFAULT_BOOTSTRAP_SENDER,
    DEFAULT_TIME_MS,
)

REPORT_SCHEMA = "zenodex.zeno_ledger.loopback_machine_b_report.v0"
DEFAULT_DOCKER_IMAGE = "python:3.12-slim"
DEFAULT_HOST_ALIAS = "host.docker.internal"


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"{path} must decode to a JSON object")
    return value


def _run_checked(
    command: list[str],
    *,
    env: dict[str, str] | None = None,
    stdout_path: Path | None = None,
) -> subprocess.CompletedProcess[str]:
    display_command = _display_command(command)
    print("+ " + display_command, flush=True)
    proc = subprocess.run(
        command,
        cwd=ROOT,
        env=env,
        text=True,
        capture_output=True,
        check=False,
    )
    if stdout_path is not None:
        stdout_path.parent.mkdir(parents=True, exist_ok=True)
        stdout_path.write_text(
            proc.stdout
            + (("\nSTDERR:\n" + proc.stderr) if proc.stderr else ""),
            encoding="utf-8",
        )
    if proc.returncode != 0:
        raise RuntimeError(
            "command failed with exit code "
            f"{proc.returncode}: {display_command}\n"
            f"stdout:\n{proc.stdout}\n"
            f"stderr:\n{proc.stderr}"
        )
    return proc


def _display_command(command: list[str]) -> str:
    redacted = []
    for item in command:
        if item.startswith("ZENO_LEDGER_WRITER_TOKEN="):
            redacted.append("ZENO_LEDGER_WRITER_TOKEN=<redacted>")
        elif "\n" in item:
            redacted.append("<inline-script>")
        else:
            redacted.append(item)
    return shlex.join(redacted)


def _start_process(command: list[str], *, env: dict[str, str] | None, log_path: Path) -> subprocess.Popen[str]:
    print("+ " + _display_command(command) + f"  # log: {log_path}", flush=True)
    log_path.parent.mkdir(parents=True, exist_ok=True)
    log_file = log_path.open("w", encoding="utf-8")
    try:
        proc = subprocess.Popen(
            command,
            cwd=ROOT,
            env=env,
            text=True,
            stdout=log_file,
            stderr=subprocess.STDOUT,
            start_new_session=True,
        )
    finally:
        log_file.close()
    return proc


def _stop_process(proc: subprocess.Popen[str] | None) -> None:
    if proc is None or proc.poll() is not None:
        return
    proc.terminate()
    try:
        proc.wait(timeout=5)
    except subprocess.TimeoutExpired:
        proc.kill()
        proc.wait(timeout=5)


def _free_port() -> int:
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
        sock.bind(("127.0.0.1", 0))
        return int(sock.getsockname()[1])


def _wait_json_url(url: str, *, timeout_seconds: float = 30.0) -> dict[str, Any]:
    deadline = time.monotonic() + timeout_seconds
    last_error: Exception | None = None
    while time.monotonic() < deadline:
        try:
            with urlopen(url, timeout=2) as response:  # noqa: S310 - local test harness URL
                value = json.loads(response.read().decode("utf-8"))
            if not isinstance(value, dict):
                raise ValueError(f"{url} did not return a JSON object")
            return value
        except Exception as exc:  # pragma: no cover - timing dependent
            last_error = exc
            time.sleep(0.25)
    raise RuntimeError(f"timed out waiting for {url}: {last_error}")


def _post_json_url(url: str, value: dict[str, object], *, bearer_token: str | None = None) -> dict[str, Any]:
    headers = {"Content-Type": "application/json"}
    if bearer_token is not None:
        headers["Authorization"] = f"Bearer {bearer_token}"
    request = Request(
        url,
        data=json.dumps(value, sort_keys=True).encode("utf-8"),
        headers=headers,
        method="POST",
    )
    with urlopen(request, timeout=30) as response:  # noqa: S310 - local test harness URL
        if response.status != HTTPStatus.OK:
            raise RuntimeError(f"{url} returned HTTP {response.status}")
        obj = json.loads(response.read().decode("utf-8"))
    if not isinstance(obj, dict):
        raise ValueError(f"{url} must return a JSON object")
    return obj


def _git_commit_sha() -> str:
    proc = _run_checked(["git", "rev-parse", "HEAD"])
    commit = proc.stdout.strip()
    if len(commit) != 40:
        raise ValueError("git rev-parse HEAD did not return a 40-hex commit")
    return commit


def _container_script(
    *,
    config_url: str,
    peer_url: str,
    commit_sha: str,
) -> str:
    return textwrap.dedent(
        f"""\
        set -eu
        BUNDLE_ROOT=/out/container_tmp/zeno-ledger-public-testnet-synced
        DATA_DIR=/out/container_tmp/zeno-ledger-node-b
        rm -rf "$BUNDLE_ROOT" "$DATA_DIR"
        mkdir -p /out/evidence /out/logs /out/container_tmp
        VENV=/out/container_tmp/venv
        if [ ! -x "$VENV/bin/python" ]; then
          python3 -m venv "$VENV"
        fi
        PYTHON="$VENV/bin/python"

        "$PYTHON" -m pip install --no-cache-dir --require-hashes -r requirements-core.lock.txt \\
          > /out/logs/machine_b_pip_install.log

        "$PYTHON" tools/zeno_ledger_node.py join-network \\
          --config-url {shlex.quote(config_url)} \\
          --node-id operator-b \\
          --bundle-root "$BUNDLE_ROOT" \\
          --data-dir "$DATA_DIR" \\
          --submit-peer-auth-token-env ZENO_LEDGER_WRITER_TOKEN \\
          > /out/logs/machine_b_join.json

        "$PYTHON" tools/zeno_ledger_node.py check-peers \\
          --data-dir "$DATA_DIR" \\
          --peer-url {shlex.quote(peer_url)} \\
          > /out/logs/machine_b_pre_pull_peer_check.json

        "$PYTHON" tools/zeno_ledger_node.py pull-live \\
          --data-dir "$DATA_DIR" \\
          --peer-url {shlex.quote(peer_url)} \\
          > /out/logs/machine_b_pull_1.json

        "$PYTHON" tools/zeno_ledger_node.py check-peers \\
          --data-dir "$DATA_DIR" \\
          --peer-url {shlex.quote(peer_url)} \\
          > /out/logs/machine_b_post_pull_peer_check.json

        "$PYTHON" tools/zeno_ledger_node.py serve \\
          --data-dir "$DATA_DIR" \\
          --host 127.0.0.1 \\
          --port 8788 \\
          --enable-testnet-intake \\
          --enable-testnet-faucet \\
          --expose-testnet-faucet-http \\
          --write-auth-token-env ZENO_LEDGER_WRITER_TOKEN \\
          --submit-peer-url {shlex.quote(peer_url)} \\
          --submit-peer-auth-token-env ZENO_LEDGER_WRITER_TOKEN \\
          > /out/logs/machine_b_serve.log 2>&1 &
        SERVER_PID="$!"
        trap 'kill "$SERVER_PID" 2>/dev/null || true' EXIT

        "$PYTHON" - <<'PY'
        import json
        import time
        from urllib.request import urlopen

        deadline = time.monotonic() + 30
        last = None
        while time.monotonic() < deadline:
            try:
                with urlopen("http://127.0.0.1:8788/network", timeout=2) as response:
                    value = json.loads(response.read().decode("utf-8"))
                if value.get("ok") is True:
                    break
            except Exception as exc:
                last = exc
                time.sleep(0.25)
        else:
            raise SystemExit(f"Machine B server did not become ready: {{last}}")
        PY

        "$PYTHON" - <<'PY' > /out/evidence/machine_b_forwarded_faucet.json
        import json
        import os
        from urllib.request import Request, urlopen

        payload = {{
            "to_pubkey": "{DEFAULT_BOOTSTRAP_SENDER}",
            "asset": "{DEFAULT_ASSET0}",
            "amount": 77,
            "time_ms": {DEFAULT_TIME_MS + 1_001_000},
            "tx_id": "loopback-machine-b-forwarded-faucet-v0",
            "local_fixture_mode": True,
        }}
        request = Request(
            "http://127.0.0.1:8788/faucet",
            data=json.dumps(payload, sort_keys=True).encode("utf-8"),
            headers={{
                "Authorization": "Bearer " + os.environ["ZENO_LEDGER_WRITER_TOKEN"],
                "Content-Type": "application/json",
            }},
            method="POST",
        )
        with urlopen(request, timeout=30) as response:
            print(json.dumps(json.loads(response.read().decode("utf-8")), indent=2, sort_keys=True))
        PY

        "$PYTHON" tools/zeno_ledger_node.py pull-live \\
          --data-dir "$DATA_DIR" \\
          --peer-url {shlex.quote(peer_url)} \\
          > /out/logs/machine_b_pull_2.json

        "$PYTHON" tools/zeno_ledger_node.py check-peers \\
          --data-dir "$DATA_DIR" \\
          --peer-url {shlex.quote(peer_url)} \\
          > /out/logs/machine_b_final_peer_check.json

        "$PYTHON" tools/build_zeno_ledger_node_evidence_input.py \\
          --data-dir "$DATA_DIR" \\
          --network-config "$DATA_DIR/public_network_config.json" \\
          --machine-out /out/evidence/machine_b.json \\
          --attestation-out /out/evidence/machine_b_watcher_attestation.json \\
          --commit-sha {shlex.quote(commit_sha)} \\
          --pretty \\
          > /out/logs/machine_b_evidence_report.json
        """
    )


def _docker_cleanup_tree(path: Path, *, image: str) -> None:
    parent = path.resolve().parent
    target = f"/cleanup-root/{path.name}"
    _run_checked(
        [
            "docker",
            "run",
            "--rm",
            "-v",
            f"{parent}:/cleanup-root",
            image,
            "rm",
            "-rf",
            "--",
            target,
        ]
    )


def _remove_tree(path: Path, *, docker_image: str) -> None:
    try:
        shutil.rmtree(path)
    except PermissionError:
        _docker_cleanup_tree(path, image=docker_image)


def _docker_command(
    *,
    image: str,
    host_alias: str,
    add_host_gateway: bool,
    out_dir: Path,
    container_script: str,
) -> list[str]:
    command = ["docker", "run", "--rm", "--user", f"{os.getuid()}:{os.getgid()}"]
    if add_host_gateway:
        command.extend(["--add-host", f"{host_alias}:host-gateway"])
    command.extend(
        [
            "-e",
            "PYTHONDONTWRITEBYTECODE=1",
            "-e",
            "ZENO_LEDGER_WRITER_TOKEN",
            "-v",
            f"{ROOT}:/repo:ro",
            "-v",
            f"{out_dir.resolve()}:/out",
            "-w",
            "/repo",
            image,
            "sh",
            "-eu",
            "-c",
            container_script,
        ]
    )
    return command


def run_loopback_machine_b_v0(
    *,
    out_dir: Path,
    docker_image: str,
    host_alias: str,
    add_host_gateway: bool,
    keep_services: bool,
) -> dict[str, Any]:
    commit_sha = _git_commit_sha()
    if out_dir.exists():
        _remove_tree(out_dir, docker_image=docker_image)
    bundle_root = out_dir / "machine_a_bundle"
    machine_a_data = out_dir / "machine_a_data"
    evidence_dir = out_dir / "evidence"
    logs_dir = out_dir / "logs"
    out_dir.mkdir(parents=True, exist_ok=True)

    mirror_port = _free_port()
    node_port = _free_port()
    writer_token = secrets.token_urlsafe(32)
    config_url_container = f"http://{host_alias}:{mirror_port}/public_network_config.json"
    peer_url_container = f"http://{host_alias}:{node_port}"
    config_url_host = f"http://127.0.0.1:{mirror_port}/public_network_config.json"
    peer_url_host = f"http://127.0.0.1:{node_port}"

    machine_a_proc: subprocess.Popen[str] | None = None
    mirror_proc: subprocess.Popen[str] | None = None
    try:
        _run_checked(
            [
                sys.executable,
                "tools/zeno_ledger_node.py",
                "bootstrap",
                "--out-dir",
                str(bundle_root),
            ],
            stdout_path=logs_dir / "machine_a_bootstrap.json",
        )
        _run_checked(
            [
                sys.executable,
                "tools/zeno_ledger_node.py",
                "write-network-config",
                "--bundle-root",
                str(bundle_root),
                "--mirror-base-url",
                f"http://{host_alias}:{mirror_port}/",
                "--writer-url",
                peer_url_container,
                "--node-port",
                "8788",
                "--out",
                str(bundle_root / "public_network_config.json"),
            ],
            stdout_path=logs_dir / "machine_a_public_network_config.json",
        )

        mirror_proc = _start_process(
            [
                sys.executable,
                "-m",
                "http.server",
                str(mirror_port),
                "--bind",
                "0.0.0.0",
                "--directory",
                str(bundle_root),
            ],
            env=os.environ.copy(),
            log_path=logs_dir / "machine_a_mirror.log",
        )
        peer_attestation = bundle_root / "bootstrap" / "watcher_attestations" / "bootstrap_range_1_5.json"
        node_env = {**os.environ.copy(), "ZENO_LEDGER_WRITER_TOKEN": writer_token}
        machine_a_proc = _start_process(
            [
                sys.executable,
                "tools/zeno_ledger_node.py",
                "run",
                "--bundle-root",
                str(bundle_root),
                "--node-id",
                "operator-a",
                "--data-dir",
                str(machine_a_data),
                "--peer-watcher-attestation",
                str(peer_attestation),
                "--serve",
                "--host",
                "0.0.0.0",
                "--port",
                str(node_port),
                "--enable-testnet-intake",
                "--enable-testnet-faucet",
                "--expose-testnet-faucet-http",
                "--write-auth-token-env",
                "ZENO_LEDGER_WRITER_TOKEN",
            ],
            env=node_env,
            log_path=logs_dir / "machine_a_node.log",
        )

        _wait_json_url(config_url_host)
        _wait_json_url(f"{peer_url_host}/network", timeout_seconds=240)
        host_faucet = _post_json_url(
            f"{peer_url_host}/faucet",
            {
                "to_pubkey": DEFAULT_BOOTSTRAP_SENDER,
                "asset": DEFAULT_ASSET0,
                "amount": 123,
                "time_ms": DEFAULT_TIME_MS + 1_000_000,
                "tx_id": "loopback-machine-a-host-faucet-v0",
                "local_fixture_mode": True,
            },
            bearer_token=writer_token,
        )
        _write_json(evidence_dir / "machine_a_host_faucet.json", host_faucet)

        container_script = _container_script(
            config_url=config_url_container,
            peer_url=peer_url_container,
            commit_sha=commit_sha,
        )
        (logs_dir / "machine_b_container_script.sh").write_text(container_script, encoding="utf-8")
        docker_command = _docker_command(
            image=docker_image,
            host_alias=host_alias,
            add_host_gateway=add_host_gateway,
            out_dir=out_dir,
            container_script=container_script,
        )
        docker_env = {**os.environ.copy(), "ZENO_LEDGER_WRITER_TOKEN": writer_token}
        _run_checked(docker_command, env=docker_env, stdout_path=logs_dir / "machine_b_docker.log")

        _run_checked(
            [
                sys.executable,
                "tools/build_zeno_ledger_node_evidence_input.py",
                "--data-dir",
                str(machine_a_data),
                "--network-config",
                str(bundle_root / "public_network_config.json"),
                "--machine-out",
                str(evidence_dir / "machine_a.json"),
                "--attestation-out",
                str(evidence_dir / "machine_a_watcher_attestation.json"),
                "--commit-sha",
                commit_sha,
                "--pretty",
            ],
            stdout_path=logs_dir / "machine_a_evidence_report.json",
        )

        forwarded_faucet = _load_json(evidence_dir / "machine_b_forwarded_faucet.json")
        final_peer_check = _load_json(logs_dir / "machine_b_final_peer_check.json")
        token_test_result = {
            "ok": (
                host_faucet.get("ok") is True
                and forwarded_faucet.get("ok") is True
                and final_peer_check.get("ok") is True
            ),
            "status": "accepted",
            "mode": "docker_loopback_machine_b",
            "asset": DEFAULT_ASSET0,
            "host_faucet_height": host_faucet.get("height"),
            "forwarded_faucet_height": forwarded_faucet.get("height"),
            "final_peer_check": final_peer_check,
        }
        if token_test_result["ok"] is not True:
            token_test_result["status"] = "rejected"
        _write_json(evidence_dir / "token_test_result.json", token_test_result)

        _run_checked(
            [
                sys.executable,
                "tools/build_zeno_ledger_two_machine_evidence.py",
                "--machine-a",
                str(evidence_dir / "machine_a.json"),
                "--machine-b",
                str(evidence_dir / "machine_b.json"),
                "--token-test-result",
                str(evidence_dir / "token_test_result.json"),
                "--watcher-attestation",
                str(evidence_dir / "machine_a_watcher_attestation.json"),
                "--watcher-attestation",
                str(evidence_dir / "machine_b_watcher_attestation.json"),
                "--accepted-tx-count",
                "2",
                "--rejected-tx-count",
                "0",
                "--latest-pushed-commit-sha",
                commit_sha,
                "--expected-commit",
                commit_sha,
                "--out",
                str(evidence_dir / "two_machine_evidence.json"),
            ],
            stdout_path=logs_dir / "two_machine_evidence_build_report.json",
        )
        validation_report = _run_checked(
            [
                sys.executable,
                "tools/check_zeno_ledger_two_machine_evidence.py",
                str(evidence_dir / "two_machine_evidence.json"),
                "--expected-commit",
                commit_sha,
            ],
            stdout_path=logs_dir / "two_machine_evidence_check_report.json",
        )
        validation = json.loads(validation_report.stdout)

        report = {
            "schema": REPORT_SCHEMA,
            "ok": validation.get("ok") is True,
            "status": "accepted" if validation.get("ok") is True else "rejected",
            "mode": "docker_loopback_machine_b",
            "commit_sha": commit_sha,
            "out_dir": str(out_dir),
            "docker_image": docker_image,
            "host_alias": host_alias,
            "machine_a": {
                "config_url_for_container": config_url_container,
                "peer_url_for_container": peer_url_container,
                "mirror_port": mirror_port,
                "node_port": node_port,
            },
            "evidence": {
                "machine_a": str(evidence_dir / "machine_a.json"),
                "machine_b": str(evidence_dir / "machine_b.json"),
                "machine_a_watcher_attestation": str(evidence_dir / "machine_a_watcher_attestation.json"),
                "machine_b_watcher_attestation": str(evidence_dir / "machine_b_watcher_attestation.json"),
                "token_test_result": str(evidence_dir / "token_test_result.json"),
                "two_machine_evidence": str(evidence_dir / "two_machine_evidence.json"),
            },
            "validation_report": validation,
            "limits": [
                "Docker loopback proves a clean Machine B can join through an HTTP network boundary.",
                "It does not prove that a separate physical laptop can traverse a hotspot or router.",
            ],
        }
        _write_json(out_dir / "loopback_machine_b_report.json", report)
        return report
    finally:
        if not keep_services:
            _stop_process(machine_a_proc)
            _stop_process(mirror_proc)


def main(argv: list[str] | None = None) -> int:
    default_out = Path(tempfile.gettempdir()) / f"zeno-ledger-loopback-machine-b-{int(time.time())}"
    parser = argparse.ArgumentParser(description="Run a Docker-isolated Machine B ZenoLedger test")
    parser.add_argument("--out-dir", type=Path, default=default_out)
    parser.add_argument("--docker-image", default=DEFAULT_DOCKER_IMAGE)
    parser.add_argument("--host-alias", default=DEFAULT_HOST_ALIAS)
    parser.add_argument(
        "--no-add-host-gateway",
        action="store_true",
        help="skip Docker's host-gateway add-host mapping, useful if the runtime already resolves host.docker.internal",
    )
    parser.add_argument(
        "--keep-services",
        action="store_true",
        help="leave Machine A host services running after the report is built",
    )
    args = parser.parse_args(argv)

    try:
        report = run_loopback_machine_b_v0(
            out_dir=args.out_dir,
            docker_image=args.docker_image,
            host_alias=args.host_alias,
            add_host_gateway=not args.no_add_host_gateway,
            keep_services=args.keep_services,
        )
    except Exception as exc:
        report = {
            "schema": REPORT_SCHEMA,
            "ok": False,
            "status": "rejected",
            "errors": [str(exc)],
        }
        if args.out_dir is not None:
            _write_json(args.out_dir / "loopback_machine_b_report.json", report)
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report.get("ok") is True else 1


if __name__ == "__main__":
    raise SystemExit(main())
