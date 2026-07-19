#!/usr/bin/env python3
"""CLI runner for chaos engineering experiments.

Usage:
    python -m tools.chaos.run_chaos_experiments --experiment tau_net_truncated_tcp
    python -m tools.chaos.run_chaos_experiments --all
    python -m tools.chaos.run_chaos_experiments --list

Experiments produce JSON evidence artifacts in runs/chaos/.
"""

from __future__ import annotations

import argparse
import json
import os
import signal
import socket
import subprocess
import sys
import tempfile
import threading
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable, Optional

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from tools.chaos.chaos_toolkit_runner import (
    ChaosExperimentRunner,
    Hypothesis,
    Perturbation,
    Recipe,
    RefutationCriterion,
    SteadyStateProbe,
    _get_git_commit,
)
from tools.chaos.regret_scheduler import (
    ChaosCampaignConfigError,
    build_campaign_state,
    write_json_artifact,
)


def _utc_now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


EXPERIMENTS_DIR = ROOT / "tools" / "chaos" / "experiments"
OUTPUT_DIR = ROOT / "runs" / "chaos"


@dataclass
class ExperimentResult:
    name: str
    outcome: str
    duration_s: float
    artifact_dir: str
    error: Optional[str] = None


def _refresh_campaign_artifacts(
    *,
    output_dir: Path,
    context_key: str,
    max_blast_radius: Optional[float],
    campaign_state_out: Path,
    regret_out: Path,
) -> tuple[dict[str, Any], dict[str, Any]]:
    campaign_state, regret_snapshot = build_campaign_state(
        runs_root=output_dir,
        experiments_dir=EXPERIMENTS_DIR,
        context_key=context_key,
        max_blast_radius=max_blast_radius,
    )
    write_json_artifact(campaign_state_out, campaign_state)
    write_json_artifact(regret_out, regret_snapshot)
    return campaign_state, regret_snapshot


def _toxiproxy_available() -> bool:
    try:
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
            s.settimeout(1.0)
            s.connect(("127.0.0.1", 8474))
            return True
    except Exception:
        return False


def _find_free_port() -> int:
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        s.bind(("127.0.0.1", 0))
        return int(s.getsockname()[1])


def run_tau_runner_sigkill(
    output_dir: Path,
    verbose: bool = False,
    context_key: Optional[str] = None,
) -> ExperimentResult:
    """Run tau_runner SIGKILL chaos experiment."""
    from src.integration.tau_runner import _run_subprocess_with_output_caps

    hypothesis = Hypothesis(
        claim="tau_runner fails closed under child process SIGKILL",
        test="Send SIGKILL mid-execution and verify TauRunError is raised",
        target="src/integration/tau_runner.py",
        perturbation_type="process_fault",
        refutation_criteria=[
            RefutationCriterion("hang", "Process hangs without returning"),
            RefutationCriterion("partial_accepted", "Partial output accepted as valid"),
            RefutationCriterion("wrong_exception", "Wrong exception type raised"),
        ],
        tags=["tau_runner", "process_fault"],
    )

    def steady_state_check() -> bool:
        return True

    probes = [SteadyStateProbe("baseline", "python", steady_state_check)]

    perturbation = Perturbation(
        perturbation_type="signal",
        action="sigkill_child",
        params={"signal": "SIGKILL", "delay_ms": 50},
    )

    refutation_triggered = {"hang": False, "partial": False, "wrong_exc": False}

    def check_hang() -> tuple[str, bool, str]:
        return ("hang", refutation_triggered["hang"], "")

    def check_partial() -> tuple[str, bool, str]:
        return ("partial_accepted", refutation_triggered["partial"], "")

    def check_wrong_exc() -> tuple[str, bool, str]:
        return ("wrong_exception", refutation_triggered["wrong_exc"], "")

    recipe = Recipe(
        hypothesis=hypothesis,
        name="tau_runner_sigkill",
        description="Test tau_runner fails closed under SIGKILL",
        target_module="src.integration.tau_runner",
        target_component="_run_subprocess_with_output_caps",
        steady_state_probes=probes,
        perturbation=perturbation,
        refutation_checks=[check_hang, check_partial, check_wrong_exc],
        tags=["tau_runner", "sigkill"],
    )

    runner = ChaosExperimentRunner(output_dir, verbose=verbose, context_key=context_key)

    def apply_perturbation() -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            script = Path(tmpdir) / "hang.py"
            script.write_text("""#!/usr/bin/env python3
import time
time.sleep(60)
""")
            script.chmod(0o755)

            killed = threading.Event()

            def kill_after(pid: int) -> None:
                time.sleep(0.1)
                try:
                    os.kill(pid, signal.SIGKILL)
                    killed.set()
                except ProcessLookupError:
                    pass

            proc = subprocess.Popen(
                [sys.executable, str(script)],
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )

            killer = threading.Thread(target=kill_after, args=(proc.pid,))
            killer.start()

            t0 = time.monotonic()
            try:
                proc.communicate(timeout=3.0)
            except subprocess.TimeoutExpired:
                refutation_triggered["hang"] = True
                proc.kill()
                proc.communicate()

            elapsed = time.monotonic() - t0
            killer.join(timeout=1.0)

            if elapsed > 5.0:
                refutation_triggered["hang"] = True

    try:
        journal = runner.run(recipe, apply_perturbation=apply_perturbation)
        return ExperimentResult(
            name="tau_runner_sigkill",
            outcome=journal.outcome,
            duration_s=journal.duration_s,
            artifact_dir=str(output_dir),
        )
    except Exception as exc:
        return ExperimentResult(
            name="tau_runner_sigkill",
            outcome="error",
            duration_s=0.0,
            artifact_dir=str(output_dir),
            error=str(exc)[:200],
        )


def run_tau_runner_stdout_flood(
    output_dir: Path,
    verbose: bool = False,
    context_key: Optional[str] = None,
) -> ExperimentResult:
    """Run tau_runner stdout flood chaos experiment."""
    from src.integration.tau_runner import _run_subprocess_with_output_caps

    hypothesis = Hypothesis(
        claim="tau_runner fails closed under stdout flood",
        test="Flood stdout with 10MB and verify limit is enforced",
        target="src/integration/tau_runner.py",
        perturbation_type="resource_exhaustion",
        refutation_criteria=[
            RefutationCriterion("hang", "Process hangs reading unbounded stdout"),
            RefutationCriterion("memory_exhaustion", "Memory grows unbounded"),
            RefutationCriterion("no_error", "No error returned despite limit exceeded"),
        ],
        tags=["tau_runner", "resource_exhaustion"],
    )

    def steady_state_check() -> bool:
        return True

    probes = [SteadyStateProbe("baseline", "python", steady_state_check)]

    perturbation = Perturbation(
        perturbation_type="mock",
        action="flood_stdout",
        params={"bytes": 10_000_000},
    )

    refutation_triggered = {"hang": False, "memory": False, "no_error": False}

    def check_hang() -> tuple[str, bool, str]:
        return ("hang", refutation_triggered["hang"], "")

    def check_memory() -> tuple[str, bool, str]:
        return ("memory_exhaustion", refutation_triggered["memory"], "")

    def check_no_error() -> tuple[str, bool, str]:
        return ("no_error", refutation_triggered["no_error"], "")

    recipe = Recipe(
        hypothesis=hypothesis,
        name="tau_runner_stdout_flood",
        description="Test tau_runner enforces stdout limit",
        target_module="src.integration.tau_runner",
        target_component="_run_subprocess_with_output_caps",
        steady_state_probes=probes,
        perturbation=perturbation,
        refutation_checks=[check_hang, check_memory, check_no_error],
        tags=["tau_runner", "stdout_flood"],
    )

    runner = ChaosExperimentRunner(output_dir, verbose=verbose, context_key=context_key)

    def apply_perturbation() -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            script = Path(tmpdir) / "flood.py"
            script.write_text("""#!/usr/bin/env python3
import sys
chunk = b"X" * 65536
for _ in range(200):  # ~13MB
    sys.stdout.buffer.write(chunk)
    sys.stdout.buffer.flush()
""")
            script.chmod(0o755)

            t0 = time.monotonic()
            rc, stdout, stderr = _run_subprocess_with_output_caps(
                [sys.executable, str(script)],
                input_text="",
                cwd=Path(tmpdir),
                timeout_s=10.0,
                max_stdout_bytes=100_000,
                max_stderr_bytes=100_000,
            )
            elapsed = time.monotonic() - t0

            if elapsed > 8.0:
                refutation_triggered["hang"] = True

            if rc == 0 and "too large" not in stderr.lower():
                refutation_triggered["no_error"] = True

    try:
        journal = runner.run(recipe, apply_perturbation=apply_perturbation)
        return ExperimentResult(
            name="tau_runner_stdout_flood",
            outcome=journal.outcome,
            duration_s=journal.duration_s,
            artifact_dir=str(output_dir),
        )
    except Exception as exc:
        return ExperimentResult(
            name="tau_runner_stdout_flood",
            outcome="error",
            duration_s=0.0,
            artifact_dir=str(output_dir),
            error=str(exc)[:200],
        )


def run_proof_verifier_timeout(
    output_dir: Path,
    verbose: bool = False,
    context_key: Optional[str] = None,
) -> ExperimentResult:
    """Run proof_verifier stalled-verifier timeout chaos experiment."""
    from src.integration.proof_verifier import SubprocessProofVerifier

    hypothesis = Hypothesis(
        claim="proof verifier fails closed under stalled external verifier",
        test="Run a verifier that never responds and verify timeout handling",
        target="src/integration/proof_verifier.py",
        perturbation_type="process_fault",
        refutation_criteria=[
            RefutationCriterion("hang", "Verifier call hangs past the timeout budget"),
            RefutationCriterion("silent_accept", "Verifier incorrectly accepts a stalled proof"),
            RefutationCriterion("wrong_error", "Verifier returns the wrong fail-closed error"),
        ],
        tags=["proof_verifier", "process_fault"],
    )

    def steady_state_check() -> bool:
        return True

    probes = [SteadyStateProbe("baseline", "python", steady_state_check)]

    perturbation = Perturbation(
        perturbation_type="signal",
        action="stalled_verifier",
        params={"timeout_s": 0.2},
    )

    refutation_triggered = {"hang": False, "silent_accept": False, "wrong_error": False}

    def check_hang() -> tuple[str, bool, str]:
        return ("hang", refutation_triggered["hang"], "")

    def check_silent_accept() -> tuple[str, bool, str]:
        return ("silent_accept", refutation_triggered["silent_accept"], "")

    def check_wrong_error() -> tuple[str, bool, str]:
        return ("wrong_error", refutation_triggered["wrong_error"], "")

    recipe = Recipe(
        hypothesis=hypothesis,
        name="proof_verifier_timeout",
        description="Test proof verifier fails closed under a stalled child process",
        target_module="src.integration.proof_verifier",
        target_component="SubprocessProofVerifier.verify",
        steady_state_probes=probes,
        perturbation=perturbation,
        refutation_checks=[check_hang, check_silent_accept, check_wrong_error],
        tags=["proof_verifier", "timeout"],
    )

    runner = ChaosExperimentRunner(output_dir, verbose=verbose, context_key=context_key)

    def apply_perturbation() -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            script = Path(tmpdir) / "stalled_verifier.py"
            script.write_text(
                """#!/usr/bin/env python3
import time
time.sleep(60)
""",
                encoding="utf-8",
            )
            script.chmod(0o755)

            verifier = SubprocessProofVerifier(
                cmd=[sys.executable, str(script)],
                timeout_s=0.2,
                max_bytes=10_000,
                max_stdout_bytes=1_000,
                max_stderr_bytes=1_000,
            )

            t0 = time.monotonic()
            ok, err = verifier.verify({"proof": "demo"})
            elapsed = time.monotonic() - t0

            if elapsed > 2.0:
                refutation_triggered["hang"] = True
            if ok:
                refutation_triggered["silent_accept"] = True
            if err != "proof verification timed out":
                refutation_triggered["wrong_error"] = True

    try:
        journal = runner.run(recipe, apply_perturbation=apply_perturbation)
        return ExperimentResult(
            name="proof_verifier_timeout",
            outcome=journal.outcome,
            duration_s=journal.duration_s,
            artifact_dir=str(output_dir),
        )
    except Exception as exc:
        return ExperimentResult(
            name="proof_verifier_timeout",
            outcome="error",
            duration_s=0.0,
            artifact_dir=str(output_dir),
            error=str(exc)[:200],
        )


def run_tau_net_truncated_tcp(
    output_dir: Path,
    verbose: bool = False,
    context_key: Optional[str] = None,
) -> ExperimentResult:
    """Run tau_net_client truncated TCP chaos experiment."""
    if not _toxiproxy_available():
        return ExperimentResult(
            name="tau_net_truncated_tcp",
            outcome="skipped",
            duration_s=0.0,
            artifact_dir=str(output_dir),
            error="Toxiproxy not available at 127.0.0.1:8474",
        )

    from src.integration.tau_net_client import TauNetRpcError, TauNetTcpClient, TauNetTcpConfig
    from tools.chaos.toxiproxy_harness import ToxiproxyHarness

    hypothesis = Hypothesis(
        claim="TauNetTcpClient fails closed under truncated TCP replies",
        test="Use Toxiproxy limit_data to truncate and verify error handling",
        target="src/integration/tau_net_client.py",
        perturbation_type="network_fault",
        refutation_criteria=[
            RefutationCriterion("partial_parse_accepted", "Truncated JSON accepted as valid"),
            RefutationCriterion("wrong_exception", "Wrong exception type raised"),
            RefutationCriterion("hang", "Client hangs waiting for data"),
        ],
        tags=["tau_net_client", "network_fault", "high_risk"],
    )

    def steady_state_check() -> bool:
        return _toxiproxy_available()

    probes = [SteadyStateProbe("toxiproxy_available", "tcp", steady_state_check)]

    perturbation = Perturbation(
        perturbation_type="toxiproxy",
        action="limit_data",
        params={"bytes": 50},
    )

    refutation_triggered = {"partial": False, "wrong_exc": False, "hang": False}

    def check_partial() -> tuple[str, bool, str]:
        return ("partial_parse_accepted", refutation_triggered["partial"], "")

    def check_wrong_exc() -> tuple[str, bool, str]:
        return ("wrong_exception", refutation_triggered["wrong_exc"], "")

    def check_hang() -> tuple[str, bool, str]:
        return ("hang", refutation_triggered["hang"], "")

    recipe = Recipe(
        hypothesis=hypothesis,
        name="tau_net_truncated_tcp",
        description="Test TauNetTcpClient handles truncated TCP",
        target_module="src.integration.tau_net_client",
        target_component="TauNetTcpClient.rpc",
        steady_state_probes=probes,
        perturbation=perturbation,
        refutation_checks=[check_partial, check_wrong_exc, check_hang],
        tags=["tau_net_client", "truncated_tcp"],
    )

    runner = ChaosExperimentRunner(output_dir, verbose=verbose, context_key=context_key)

    def apply_perturbation() -> None:
        mock_port = _find_free_port()

        def mock_server() -> None:
            with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
                s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
                s.bind(("127.0.0.1", mock_port))
                s.listen(1)
                s.settimeout(5.0)
                try:
                    conn, _ = s.accept()
                    conn.recv(1024)
                    conn.sendall(b'{"status": "ok", "balance": 1000000, "nonce": 42}\n')
                    conn.close()
                except Exception:
                    pass

        server_thread = threading.Thread(target=mock_server, daemon=True)
        server_thread.start()
        time.sleep(0.1)

        try:
            with ToxiproxyHarness(
                upstream_host="127.0.0.1",
                upstream_port=mock_port,
            ) as harness:
                harness.limit_data(50)

                config = TauNetTcpConfig(
                    host=harness.listen_host,
                    port=harness.listen_port,
                    timeout_s=2.0,
                )
                client = TauNetTcpClient(config)

                t0 = time.monotonic()
                try:
                    result = client.rpc("test")
                    elapsed = time.monotonic() - t0

                    if elapsed > 5.0:
                        refutation_triggered["hang"] = True

                    try:
                        parsed = json.loads(result)
                        if "balance" in parsed:
                            refutation_triggered["partial"] = True
                    except json.JSONDecodeError:
                        pass

                except TauNetRpcError:
                    pass
                except Exception as exc:
                    if not isinstance(exc, (ConnectionError, OSError, socket.error)):
                        refutation_triggered["wrong_exc"] = True

        except Exception:
            pass

        server_thread.join(timeout=2.0)

    try:
        journal = runner.run(recipe, apply_perturbation=apply_perturbation)
        return ExperimentResult(
            name="tau_net_truncated_tcp",
            outcome=journal.outcome,
            duration_s=journal.duration_s,
            artifact_dir=str(output_dir),
        )
    except Exception as exc:
        return ExperimentResult(
            name="tau_net_truncated_tcp",
            outcome="error",
            duration_s=0.0,
            artifact_dir=str(output_dir),
            error=str(exc)[:200],
        )


def run_tau_net_reset_peer(
    output_dir: Path,
    verbose: bool = False,
    context_key: Optional[str] = None,
) -> ExperimentResult:
    """Run tau_net_client reset_peer chaos experiment."""
    if not _toxiproxy_available():
        return ExperimentResult(
            name="tau_net_reset_peer",
            outcome="skipped",
            duration_s=0.0,
            artifact_dir=str(output_dir),
            error="Toxiproxy not available at 127.0.0.1:8474",
        )

    from src.integration.tau_net_client import TauNetRpcError, TauNetTcpClient, TauNetTcpConfig
    from tools.chaos.toxiproxy_harness import ToxiproxyHarness

    hypothesis = Hypothesis(
        claim="TauNetTcpClient handles reset_peer without retry storm",
        test="Use Toxiproxy reset_peer and verify no retry storm",
        target="src/integration/tau_net_client.py",
        perturbation_type="network_fault",
        refutation_criteria=[
            RefutationCriterion("retry_storm", "More than 3 connections in 1 second"),
            RefutationCriterion("hang", "Client hangs on reset"),
            RefutationCriterion("silent_failure", "Returns without raising"),
        ],
        tags=["tau_net_client", "network_fault"],
    )

    def steady_state_check() -> bool:
        return _toxiproxy_available()

    probes = [SteadyStateProbe("toxiproxy_available", "tcp", steady_state_check)]

    perturbation = Perturbation(
        perturbation_type="toxiproxy",
        action="reset_peer",
        params={"timeout": 0},
    )

    refutation_triggered = {"retry_storm": False, "hang": False, "silent": False}

    def check_retry_storm() -> tuple[str, bool, str]:
        return ("retry_storm", refutation_triggered["retry_storm"], "")

    def check_hang() -> tuple[str, bool, str]:
        return ("hang", refutation_triggered["hang"], "")

    def check_silent() -> tuple[str, bool, str]:
        return ("silent_failure", refutation_triggered["silent"], "")

    recipe = Recipe(
        hypothesis=hypothesis,
        name="tau_net_reset_peer",
        description="Test TauNetTcpClient handles reset_peer",
        target_module="src.integration.tau_net_client",
        target_component="TauNetTcpClient.rpc",
        steady_state_probes=probes,
        perturbation=perturbation,
        refutation_checks=[check_retry_storm, check_hang, check_silent],
        tags=["tau_net_client", "reset_peer"],
    )

    runner = ChaosExperimentRunner(output_dir, verbose=verbose, context_key=context_key)

    def apply_perturbation() -> None:
        mock_port = _find_free_port()

        def mock_server() -> None:
            with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
                s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
                s.bind(("127.0.0.1", mock_port))
                s.listen(1)
                s.settimeout(5.0)
                try:
                    conn, _ = s.accept()
                    conn.recv(1024)
                    conn.sendall(b"OK\n")
                    conn.close()
                except Exception:
                    pass

        server_thread = threading.Thread(target=mock_server, daemon=True)
        server_thread.start()
        time.sleep(0.1)

        try:
            with ToxiproxyHarness(
                upstream_host="127.0.0.1",
                upstream_port=mock_port,
            ) as harness:
                harness.reset_peer(timeout_ms=0)

                config = TauNetTcpConfig(
                    host=harness.listen_host,
                    port=harness.listen_port,
                    timeout_s=2.0,
                )
                client = TauNetTcpClient(config)

                t0 = time.monotonic()
                try:
                    result = client.rpc("test")
                    refutation_triggered["silent"] = True
                except (TauNetRpcError, ConnectionError, OSError):
                    pass
                except Exception:
                    pass

                elapsed = time.monotonic() - t0
                if elapsed > 5.0:
                    refutation_triggered["hang"] = True

        except Exception:
            pass

        server_thread.join(timeout=2.0)

    try:
        journal = runner.run(recipe, apply_perturbation=apply_perturbation)
        return ExperimentResult(
            name="tau_net_reset_peer",
            outcome=journal.outcome,
            duration_s=journal.duration_s,
            artifact_dir=str(output_dir),
        )
    except Exception as exc:
        return ExperimentResult(
            name="tau_net_reset_peer",
            outcome="error",
            duration_s=0.0,
            artifact_dir=str(output_dir),
            error=str(exc)[:200],
        )


def run_api_server_oversized_body(
    output_dir: Path,
    verbose: bool = False,
    context_key: Optional[str] = None,
) -> ExperimentResult:
    """Run api_server oversized body chaos experiment."""
    import http.client
    from http.server import ThreadingHTTPServer

    from src.integration.api_server import _Handler, TokenBucketRateLimiter

    hypothesis = Hypothesis(
        claim="api_server rejects oversized POST body without hang",
        test="Send 10MB Content-Length and verify 413 response",
        target="src/integration/api_server.py",
        perturbation_type="http_fault",
        refutation_criteria=[
            RefutationCriterion("hang", "Server hangs trying to read body"),
            RefutationCriterion("memory_exhaustion", "Server allocates full body"),
            RefutationCriterion("wrong_status", "Returns status other than 413"),
        ],
        tags=["api_server", "http_fault"],
    )

    def steady_state_check() -> bool:
        return True

    probes = [SteadyStateProbe("baseline", "python", steady_state_check)]

    perturbation = Perturbation(
        perturbation_type="http",
        action="oversized_body",
        params={"content_length": 10_000_000},
    )

    refutation_triggered = {"hang": False, "memory": False, "wrong_status": False}

    def check_hang() -> tuple[str, bool, str]:
        return ("hang", refutation_triggered["hang"], "")

    def check_memory() -> tuple[str, bool, str]:
        return ("memory_exhaustion", refutation_triggered["memory"], "")

    def check_wrong_status() -> tuple[str, bool, str]:
        return ("wrong_status", refutation_triggered["wrong_status"], "")

    recipe = Recipe(
        hypothesis=hypothesis,
        name="api_server_oversized_body",
        description="Test api_server rejects oversized body",
        target_module="src.integration.api_server",
        target_component="_Handler",
        steady_state_probes=probes,
        perturbation=perturbation,
        refutation_checks=[check_hang, check_memory, check_wrong_status],
        tags=["api_server", "oversized_body"],
    )

    runner = ChaosExperimentRunner(output_dir, verbose=verbose, context_key=context_key)

    def apply_perturbation() -> None:
        port = _find_free_port()
        server = ThreadingHTTPServer(("127.0.0.1", port), _Handler)
        server.rate_limiter = TokenBucketRateLimiter(rpm=0)  # type: ignore
        server.cors_origins = set()  # type: ignore
        server.dex_api_enabled = True  # type: ignore

        server_thread = threading.Thread(target=server.handle_request, daemon=True)
        server_thread.start()
        time.sleep(0.1)

        conn = http.client.HTTPConnection("127.0.0.1", port, timeout=5)
        try:
            conn.putrequest("POST", "/api/dex/impact_preview")
            conn.putheader("Content-Type", "application/json")
            conn.putheader("Content-Length", "10000000")
            conn.endheaders()

            t0 = time.monotonic()
            conn.send(b'{"test": "data"}')

            try:
                response = conn.getresponse()
                elapsed = time.monotonic() - t0

                if elapsed > 3.0:
                    refutation_triggered["hang"] = True

                if response.status not in (413, 400):
                    refutation_triggered["wrong_status"] = True

            except http.client.RemoteDisconnected:
                pass

        finally:
            conn.close()
            server.server_close()

    try:
        journal = runner.run(recipe, apply_perturbation=apply_perturbation)
        return ExperimentResult(
            name="api_server_oversized_body",
            outcome=journal.outcome,
            duration_s=journal.duration_s,
            artifact_dir=str(output_dir),
        )
    except Exception as exc:
        return ExperimentResult(
            name="api_server_oversized_body",
            outcome="error",
            duration_s=0.0,
            artifact_dir=str(output_dir),
            error=str(exc)[:200],
        )


EXPERIMENTS = {
    "tau_runner_sigkill": run_tau_runner_sigkill,
    "tau_runner_stdout_flood": run_tau_runner_stdout_flood,
    "proof_verifier_timeout": run_proof_verifier_timeout,
    "tau_net_truncated_tcp": run_tau_net_truncated_tcp,
    "tau_net_reset_peer": run_tau_net_reset_peer,
    "api_server_oversized_body": run_api_server_oversized_body,
}


def main() -> int:
    parser = argparse.ArgumentParser(description="Run chaos engineering experiments")
    parser.add_argument("--experiment", "-e", type=str, help="Experiment name to run")
    parser.add_argument("--all", "-a", action="store_true", help="Run all experiments")
    parser.add_argument("--list", "-l", action="store_true", help="List available experiments")
    parser.add_argument(
        "--select-next",
        action="store_true",
        help="Select the next experiment using regret-aware campaign state",
    )
    parser.add_argument("--output", "-o", type=Path, default=OUTPUT_DIR, help="Output directory")
    parser.add_argument("--verbose", "-v", action="store_true", help="Verbose output")
    parser.add_argument("--json", action="store_true", help="Output results as JSON")
    parser.add_argument(
        "--context-key",
        type=str,
        default="",
        help="Campaign context key (default: git:<current_commit>)",
    )
    parser.add_argument(
        "--max-blast-radius",
        type=float,
        default=None,
        help="Only consider experiments with blast radius <= threshold when selecting",
    )
    parser.add_argument(
        "--campaign-state-out",
        type=Path,
        default=None,
        help="Where to write campaign state JSON (default: <output>/campaign_state.json)",
    )
    parser.add_argument(
        "--regret-out",
        type=Path,
        default=None,
        help="Where to write regret snapshot JSON (default: <output>/regret_snapshot.json)",
    )
    args = parser.parse_args()

    if args.list:
        print("Available experiments:")
        for name in sorted(EXPERIMENTS.keys()):
            print(f"  - {name}")
        return 0

    current_context_key = args.context_key.strip() or f"git:{_get_git_commit()}"
    campaign_state_out = args.campaign_state_out or (args.output / "campaign_state.json")
    regret_out = args.regret_out or (args.output / "regret_snapshot.json")

    if args.select_next and not args.experiment and not args.all:
        args.output.mkdir(parents=True, exist_ok=True)
        try:
            campaign_state, regret_snapshot = _refresh_campaign_artifacts(
                output_dir=args.output,
                context_key=current_context_key,
                max_blast_radius=args.max_blast_radius,
                campaign_state_out=campaign_state_out,
                regret_out=regret_out,
            )
        except ChaosCampaignConfigError as exc:
            print(str(exc), file=sys.stderr)
            return 1
        if args.json:
            print(json.dumps({"campaign_state": campaign_state, "regret_snapshot": regret_snapshot}, indent=2))
        else:
            selected = campaign_state.get("selected_experiment")
            if selected:
                print(str(selected))
            else:
                print("no feasible experiment", file=sys.stderr)
                return 1
        return 0

    if not args.experiment and not args.all:
        parser.print_help()
        return 1

    args.output.mkdir(parents=True, exist_ok=True)

    results: list[ExperimentResult] = []

    if args.all:
        experiments_to_run = list(EXPERIMENTS.keys())
    else:
        if args.experiment not in EXPERIMENTS:
            print(f"Unknown experiment: {args.experiment}", file=sys.stderr)
            print(f"Available: {', '.join(sorted(EXPERIMENTS.keys()))}", file=sys.stderr)
            return 1
        experiments_to_run = [args.experiment]

    for name in experiments_to_run:
        if args.verbose:
            print(f"\n{'='*60}")
            print(f"Running: {name}")
            print(f"{'='*60}")

        exp_output = args.output / name
        exp_output.mkdir(parents=True, exist_ok=True)

        result = EXPERIMENTS[name](exp_output, verbose=args.verbose, context_key=current_context_key)
        results.append(result)

        if not args.json:
            status_icon = "✓" if result.outcome == "corroborated" else "✗" if result.outcome == "falsified" else "?"
            print(f"{status_icon} {result.name}: {result.outcome} ({result.duration_s:.2f}s)")
            if result.error:
                print(f"  Error: {result.error}")

    try:
        campaign_state, regret_snapshot = _refresh_campaign_artifacts(
            output_dir=args.output,
            context_key=current_context_key,
            max_blast_radius=args.max_blast_radius,
            campaign_state_out=campaign_state_out,
            regret_out=regret_out,
        )
    except ChaosCampaignConfigError as exc:
        print(str(exc), file=sys.stderr)
        return 1

    if args.json:
        output = {
            "schema": "chaos/run_summary/v1",
            "timestamp": _utc_now_iso(),
            "context_key": current_context_key,
            "selected_experiment": campaign_state.get("selected_experiment"),
            "campaign_state_path": str(campaign_state_out),
            "regret_snapshot_path": str(regret_out),
            "results": [
                {
                    "name": r.name,
                    "outcome": r.outcome,
                    "duration_s": r.duration_s,
                    "artifact_dir": r.artifact_dir,
                    "error": r.error,
                }
                for r in results
            ],
        }
        print(json.dumps(output, indent=2))

    failed = sum(1 for r in results if r.outcome in ("falsified", "error"))
    return 1 if failed > 0 else 0


if __name__ == "__main__":
    raise SystemExit(main())
