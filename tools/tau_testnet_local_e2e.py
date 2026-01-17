#!/usr/bin/env python3

from __future__ import annotations

import argparse
import os
import shlex
import socket
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Optional


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def _wait_for_tcp_hello(*, host: str, port: int, timeout_s: float) -> bool:
    deadline = time.time() + float(timeout_s)
    while time.time() < deadline:
        try:
            with socket.create_connection((host, port), timeout=0.5) as sock:
                sock.sendall(b"hello version=1\r\n")
                sock.recv(4096)
            return True
        except Exception:
            time.sleep(0.1)
    return False


@dataclass(frozen=True)
class _E2EArgs:
    host: str
    port: int
    chain_id: str
    privkey: Optional[str]
    miner_privkey: Optional[str]
    no_smoke: bool
    force_test: bool
    enable_faucet: bool
    enable_state_proof_debug: bool
    enable_state_proof_risc0: bool
    ready_timeout_s: float


def _parse_args(argv: Optional[list[str]]) -> _E2EArgs:
    parser = argparse.ArgumentParser(
        description="Run a local Tau Testnet node with the DEX app-bridge and optional smoke test"
    )
    parser.add_argument("--host", default="127.0.0.1")
    parser.add_argument("--port", type=int, default=65432)
    parser.add_argument("--chain-id", default="tau-local")
    parser.add_argument("--privkey", default=None, help="Optional: pass through to smoke test (32-byte hex)")
    parser.add_argument(
        "--miner-privkey",
        default=None,
        help="Optional: mining key (32-byte hex); defaults to --privkey or smoke default",
    )
    parser.add_argument("--no-smoke", action="store_true", help="Start the node only (do not run the smoke test)")
    parser.add_argument("--force-test", action="store_true", help="Run Tau in test mode (no Docker / no tau binary)")
    parser.add_argument("--enable-faucet", action="store_true", help="Enable DEX faucet op '4' (test-only)")
    parser.add_argument(
        "--enable-state-proof-debug",
        action="store_true",
        help="Enable debug state_proof publishing (not ZK; plumbing smoke-test only)",
    )
    parser.add_argument(
        "--enable-state-proof-risc0",
        action="store_true",
        help="Enable Risc0-backed state_proof publishing (requires Rust + Risc0 toolchain)",
    )
    parser.add_argument("--ready-timeout-s", type=float, default=10.0)
    args = parser.parse_args(argv)

    return _E2EArgs(
        host=str(args.host),
        port=int(args.port),
        chain_id=str(args.chain_id),
        privkey=(str(args.privkey) if args.privkey is not None else None),
        miner_privkey=(str(args.miner_privkey) if args.miner_privkey is not None else None),
        no_smoke=bool(args.no_smoke),
        force_test=bool(args.force_test),
        enable_faucet=bool(args.enable_faucet),
        enable_state_proof_debug=bool(args.enable_state_proof_debug),
        enable_state_proof_risc0=bool(args.enable_state_proof_risc0),
        ready_timeout_s=float(args.ready_timeout_s),
    )


def _must_exist(path: Path, *, label: str) -> None:
    if not path.is_file():
        raise SystemExit(f"missing {label}: {path}")


def _configure_tau_server_env(env: dict[str, str], *, args: _E2EArgs, root: Path) -> None:
    # Tau-testnet server listen.
    env["TAU_HOST"] = str(args.host)
    env["TAU_PORT"] = str(int(args.port))
    env.setdefault("TAU_BUFFER_SIZE", "1048576")
    env.setdefault("TAU_ENV", env.get("TAU_ENV", "development"))

    # Single-node local testing defaults (avoid connecting to the wider network).
    env.setdefault("TAU_BOOTSTRAP_PEERS", "[]")
    env.setdefault("TAU_DHT_BOOTSTRAP", "[]")

    # Enable generic app bridge and point to this repo's DEX plugin.
    env["TAU_APP_BRIDGE_SYS_PATH"] = str(root)
    env["TAU_APP_BRIDGE_MODULE"] = "src.integration.tau_testnet_dex_plugin"
    env["TAU_DEX_CHAIN_ID"] = str(args.chain_id)


def _ensure_miner_keys(env: dict[str, str], *, miner_privkey: str) -> None:
    # Ensure local mining works even if tau-testnet defaults disable MINER_PRIVKEY.
    if "TAU_MINER_PRIVKEY" not in env:
        m = str(miner_privkey).strip()
        if m.lower().startswith("0x"):
            m = m[2:]
        env["TAU_MINER_PRIVKEY"] = m

    if "TAU_MINER_PUBKEY" in env:
        return

    try:
        from src.integration.tau_net_client import (  # pylint: disable=import-outside-toplevel
            bls_pubkey_hex_from_privkey,
        )
    except Exception:
        return
    env["TAU_MINER_PUBKEY"] = bls_pubkey_hex_from_privkey(env["TAU_MINER_PRIVKEY"])


def _enable_state_proof_debug(env: dict[str, str], *, root: Path) -> None:
    gen = root / "tools" / "state_proof_debug_generate.py"
    ver = root / "tools" / "state_proof_debug_verify.py"
    env.setdefault("TAU_STATE_PROOF_GENERATE_REQUIRE", "1")
    env.setdefault("TAU_STATE_PROOF_GENERATE_CMD", f"{shlex.quote(sys.executable)} {shlex.quote(str(gen))}")
    env.setdefault("TAU_STATE_PROOF_VERIFY_CMD", f"{shlex.quote(sys.executable)} {shlex.quote(str(ver))}")
    env.setdefault("TAU_EXPECT_STATE_PROOF", "1")


def _build_risc0_state_proof_cli(*, zk_dir: Path, env: dict[str, str]) -> None:
    env.setdefault("RISC0_FORCE_BUILD", "1")
    try:
        subprocess.check_call(
            ["cargo", "build", "--release", "--offline", "-p", "tau-state-proof-risc0-cli"],
            cwd=str(zk_dir),
            env=env,
        )
    except subprocess.CalledProcessError:
        subprocess.check_call(
            ["cargo", "build", "--release", "-p", "tau-state-proof-risc0-cli"],
            cwd=str(zk_dir),
            env=env,
        )


def _enable_state_proof_risc0(env: dict[str, str], *, root: Path) -> None:
    env.setdefault("TAU_STATE_PROOF_GENERATE_REQUIRE", "1")
    env.setdefault("TAU_STATE_PROOF_SUBPROCESS_TIMEOUT_S", "300")
    env.setdefault("TAU_STATE_PROOF_MAX_STDOUT_BYTES", "6000000")

    if "TAU_STATE_PROOF_GENERATE_CMD" not in env or "TAU_STATE_PROOF_VERIFY_CMD" not in env:
        zk_dir = root / "zk" / "state_proof_risc0"
        bin_path = zk_dir / "target" / "release" / "tau-state-proof-risc0-cli"
        if not bin_path.is_file():
            _build_risc0_state_proof_cli(zk_dir=zk_dir, env=env)
        if not bin_path.is_file():
            raise SystemExit(f"missing Risc0 state proof binary: {bin_path}")
        env.setdefault("TAU_STATE_PROOF_GENERATE_CMD", str(bin_path))
        env.setdefault("TAU_STATE_PROOF_VERIFY_CMD", str(bin_path))

    env.setdefault("TAU_EXPECT_STATE_PROOF", "1")


def _spawn_tau_node(*, tau_testnet_dir: Path, env: dict[str, str]) -> subprocess.Popen[bytes]:
    # Run with tau-testnet as CWD so relative paths (e.g. genesis.tau) resolve correctly.
    cmd = [sys.executable, "server.py", "--ephemeral-identity"]
    return subprocess.Popen(cmd, cwd=str(tau_testnet_dir), env=env)


def _run_smoke_test(*, root: Path, env: dict[str, str], args: _E2EArgs) -> int:
    smoke_cmd = [
        sys.executable,
        "tools/tau_testnet_local_smoke.py",
        "--host",
        str(args.host),
        "--port",
        str(int(args.port)),
        "--chain-id",
        str(args.chain_id),
    ]
    if args.privkey:
        smoke_cmd += ["--privkey", str(args.privkey)]
    return int(subprocess.call(smoke_cmd, cwd=str(root), env=env))


def _terminate_process(proc: subprocess.Popen[bytes]) -> None:
    if proc.poll() is not None:
        return
    proc.terminate()
    try:
        proc.wait(timeout=2.0)
    except Exception:
        proc.kill()
        proc.wait(timeout=2.0)


def main(argv: Optional[list[str]] = None) -> int:
    args = _parse_args(argv)
    if not (0 <= int(args.port) <= 65535):
        raise SystemExit("invalid --port")

    root = _repo_root()
    tau_testnet_dir = root / "external" / "tau-testnet"
    _must_exist(tau_testnet_dir / "server.py", label="tau-testnet server")

    env = os.environ.copy()
    _configure_tau_server_env(env, args=args, root=root)

    smoke_default_privkey_hex = "11cebd90117355080b392cb7ef2fbdeff1150a124d29058ae48b19bebecd4f09"
    miner_privkey = args.miner_privkey or args.privkey or smoke_default_privkey_hex
    _ensure_miner_keys(env, miner_privkey=str(miner_privkey))

    if args.force_test:
        env.setdefault("TAU_FORCE_TEST", "1")
    if args.enable_faucet:
        env.setdefault("TAU_DEX_FAUCET", "1")
    if args.enable_state_proof_debug:
        _enable_state_proof_debug(env, root=root)
    if args.enable_state_proof_risc0:
        _enable_state_proof_risc0(env, root=root)

    proc = _spawn_tau_node(tau_testnet_dir=tau_testnet_dir, env=env)
    try:
        ready = _wait_for_tcp_hello(host=args.host, port=args.port, timeout_s=args.ready_timeout_s)
        if not ready:
            raise RuntimeError("node did not become ready (TCP hello timed out)")

        if args.no_smoke:
            print("node ready; press Ctrl-C to stop")
            proc.wait()
            return int(proc.returncode or 0)

        return _run_smoke_test(root=root, env=env, args=args)
    finally:
        _terminate_process(proc)


if __name__ == "__main__":
    raise SystemExit(main())
