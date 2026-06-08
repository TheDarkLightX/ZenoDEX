#!/usr/bin/env python3
"""Rigorous RISC0 prove-time benchmark harness for the unified ZenoDEX proof CLI.

Measures STEADY-STATE prove time only. The CLI + guest ELF are built ONCE up
front (`cargo build --release -p tau-state-proof-risc0-cli`); that cost is
recorded SEPARATELY as ``build_cost_s``. Each subsequent prove run is a single
exec of the already-built binary, so build/compile time is never counted as
prove time.

Methodology (fail-closed throughout):

1. Build once, then time the full prove EXEC of the prebuilt binary. The timed
   figure is reported as ``prove_exec_wall_s`` (not "prove()"): it is the
   end-to-end wall time of one CLI exec — process spawn, stdin JSON parse,
   ELF/proving-system load, the STARK prove() itself, receipt serialize, and
   stdout write. For a multi-second STARK the fixed per-exec overhead (fork/exec
   + executor setup, typically tens of ms) is small, but it is a real positive
   bias. To let a reader split proving from overhead we also measure an
   ``exec_overhead_s`` floor once (the wall time of a fast non-proving exec); it
   is reported, never subtracted from the prove figure.
2. Per surface (spot, perps_np, zusd, clob): one DETERMINISTIC fixed request,
   reused verbatim for every repetition.
3. N repetitions per surface (TIMED AFTER the warmup window); report
   min/median/mean/p99/stdev (seconds). The default ``--warmup`` is 1 so the
   cold first prove (cold page cache, first-touch alloc, CPU freq ramp) is
   discarded and the reported stats are genuinely steady-state. NOTE: ``p99`` at
   small N is the nearest-rank max (p99 of N<=100 == max); a meaningful tail
   percentile requires a larger ``--reps`` — at the default N the p99 column is
   the observed maximum, not a tail estimate.
4. Separate PROVE from VERIFY: ONE representative ``verify_ms_single`` per
   surface for context. It is a SINGLE sample (n=1), NOT a distribution — unlike
   the prove block it has no min/median/p99/stdev and is not directly comparable.
5. RISC0_DEV_MODE guard: if RISC0_DEV_MODE is truthy, REFUSE and exit non-zero
   (dev mode emits instant fake receipts). Record ``dev_mode: false`` otherwise.
6. Fail-closed: build failure / missing toolchain / prove error / timeout =>
   ``status: "unmeasured"`` with a reason and NO fabricated number. VERIFY also
   gates: if a surface CAN build a verify request (it supports verify) but the
   representative verify does not return ``ok`` — rejected receipt, rc!=0,
   invalid JSON, timeout, or the binding proof itself failing to regenerate —
   the surface is downgraded to ``unmeasured`` with a verify reason and NO prove
   number is reported. Verify is treated as optional ONLY for a surface that
   cannot assemble a verify request at all (none currently). "Couldn't measure"
   is distinct from a measurement.
7. Record environment: CPU model/count, resolved RISC0 version (Cargo.lock),
   git commit, and the load-affecting prover knobs (RISC0_PROVER backend,
   RAYON_NUM_THREADS, 1-/5-/15-min load average). Two runs under different
   background load or thread counts produce materially different numbers; these
   knobs are recorded so a figure is reproducible/comparable. Hostname-free.
   JSON to stdout, human logs to stderr, optional markdown table (--markdown)
   and a writable results path (--out).
8. --self-test: validates the harness LOGIC (timing capture, stats, JSON +
   markdown shape, dev-mode guard, verify-gate fail-closed, fail-closed on
   simulated build failure) on a trivial fast operation, WITHOUT a real STARK.
   Exits 0 in < 5s.

Design: small pure functions in the functional core (stats, predicates,
rendering, report assembly); a thin imperative shell (subprocess, env, file I/O,
sys.exit). The build runner and the per-surface prove/verify runners are
injected callables so the self-test can swap in fast mocks.
"""

from __future__ import annotations

import argparse
import contextlib
import importlib
import json
import os
import re
import statistics
import subprocess
import sys
import time
from collections.abc import Callable, Iterator
from dataclasses import dataclass, field
from pathlib import Path
from types import ModuleType
from typing import Any

# --------------------------------------------------------------------------- #
# Constants                                                                    #
# --------------------------------------------------------------------------- #

REPO_DEFAULT = Path(__file__).resolve().parents[1]
CLI_MANIFEST_REL = "zk/state_proof_risc0/Cargo.toml"
CLI_LOCK_REL = "zk/state_proof_risc0/Cargo.lock"
CLI_PACKAGE = "tau-state-proof-risc0-cli"
CLI_BIN_REL = Path("release") / CLI_PACKAGE

SURFACES = ("spot", "perps_np", "zusd", "clob")
SCHEMA = "zenodex.bench_prove_times.v1"

# State hashes / chain ids reused by the deterministic requests.
SPOT_STATE_HASH = "11" * 32
CLOB_STATE_HASH = "33" * 32
CLOB_CHAIN_ID = "zenodex-local-risc0-smoke-1"

# Pure spot "empty" snapshot (kept inline to avoid the heavy src.integration
# imports the spot smoke pulls in for its non-empty cases).
SPOT_EMPTY_SNAPSHOT: dict[str, Any] = {
    "version": 1,
    "balances": [],
    "pools": [],
    "lp_balances": [],
    "fee_accumulator": {"dust": 0},
    "vault": None,
    "oracle": None,
}


# --------------------------------------------------------------------------- #
# Logging helper (human logs ALWAYS to stderr; stdout is reserved for JSON)    #
# --------------------------------------------------------------------------- #


def log(msg: str) -> None:
    print(msg, file=sys.stderr, flush=True)


# --------------------------------------------------------------------------- #
# Shell: scoped module import (no permanent sys.path mutation)                 #
# --------------------------------------------------------------------------- #


@contextlib.contextmanager
def _sys_path_prepended(path: Path) -> Iterator[None]:
    """Temporarily prepend ``path`` to ``sys.path``, restoring it on exit.

    Avoids the global-state leak of an unrestored ``sys.path.insert`` inside the
    otherwise-functional plan builders: the entry is removed (only if we added
    it) once the ``with`` block ends, so importing a smoke module cannot
    permanently shadow other modules.
    """
    entry = str(path)
    already_present = entry in sys.path
    if not already_present:
        sys.path.insert(0, entry)
    try:
        yield
    finally:
        if not already_present:
            with contextlib.suppress(ValueError):
                sys.path.remove(entry)


def _import_smoke_module(repo: Path, module_name: str) -> ModuleType:
    """Import a ``tools/`` smoke module under a scoped ``sys.path`` (shell-only)."""
    with _sys_path_prepended(repo / "tools"):
        return importlib.import_module(module_name)


# --------------------------------------------------------------------------- #
# Pure core: dev-mode predicate                                                #
# --------------------------------------------------------------------------- #


def dev_mode_is_truthy(value: str | None) -> bool:
    """Return True iff ``value`` indicates RISC0 dev mode is ENABLED.

    Pure predicate. Truthy values are ``"1"``, ``"true"``, ``"yes"``, ``"on"``
    (case-insensitive). ``None``, ``""``, ``"0"``, ``"false"`` are FALSE so that
    a literal ``RISC0_DEV_MODE=0`` proceeds (do NOT use ``bool(env)`` which would
    treat ``"0"`` as truthy and wrongly refuse).
    """
    if value is None:
        return False
    return value.strip().lower() in {"1", "true", "yes", "on"}


# --------------------------------------------------------------------------- #
# Pure core: statistics                                                        #
# --------------------------------------------------------------------------- #


def percentile(samples: list[float], pct: float) -> float:
    """Nearest-rank percentile (no interpolation, no numpy).

    idx = ceil(pct/100 * n) - 1, clamped to [0, n-1] over the sorted samples.
    p99 of N=5 therefore returns the max. Empty input raises ValueError.
    """
    if not samples:
        raise ValueError("percentile of empty sample set")
    if not (0.0 <= pct <= 100.0):
        raise ValueError(f"percentile out of range: {pct}")
    ordered = sorted(samples)
    n = len(ordered)
    rank = -(-int(round(pct * n * 1_000_000)) // 100_000_000)  # ceil(pct/100*n)
    idx = min(max(rank - 1, 0), n - 1)
    return ordered[idx]


def summarize_stats(samples: list[float]) -> dict[str, Any]:
    """Compute min/median/mean/p99/stdev (seconds) for a non-empty sample set.

    Pure. ``stdev`` is the sample standard deviation; for n < 2 it is 0.0
    (statistics.stdev raises on a single sample). ``p99_s`` is nearest-rank: at
    small N it equals the observed maximum (p99 of N<=100 == max) and is NOT a
    tail estimate — a meaningful tail percentile needs a much larger N. The
    ``p99_is_max`` flag makes this explicit for any consumer.
    """
    if not samples:
        raise ValueError("summarize_stats of empty sample set")
    n = len(samples)
    return {
        "n": n,
        "min_s": min(samples),
        "median_s": statistics.median(samples),
        "mean_s": statistics.fmean(samples),
        "p99_s": percentile(samples, 99.0),
        # Nearest-rank p99 collapses to the max until N is large; flag it so a
        # reader never mistakes the small-N p99 for a real tail estimate.
        "p99_is_max": percentile(samples, 99.0) == max(samples),
        "stdev_s": statistics.stdev(samples) if n >= 2 else 0.0,
    }


# --------------------------------------------------------------------------- #
# Pure core: sample collection over an injected runner                         #
# --------------------------------------------------------------------------- #


@dataclass
class SampleRun:
    """Outcome of a single timed invocation."""

    duration_s: float
    ok: bool
    reason: str = ""


def collect_samples(
    run_one: Callable[[int], SampleRun],
    n: int,
    *,
    warmup: int = 0,
) -> tuple[list[float], list[str]]:
    """Run ``run_one`` ``warmup + n`` times; return (kept_durations, failures).

    ``run_one(i)`` returns a SampleRun. Only ``ok`` runs after the warmup window
    contribute a duration; any failed run records a reason and contributes NO
    duration (a crashed/fast prove must never look like throughput).
    """
    if n < 1:
        raise ValueError("n must be >= 1")
    if warmup < 0:
        raise ValueError("warmup must be >= 0")
    durations: list[float] = []
    failures: list[str] = []
    for i in range(warmup + n):
        result = run_one(i)
        if i < warmup:
            if not result.ok:
                failures.append(f"warmup[{i}]: {result.reason}")
            continue
        if result.ok:
            durations.append(result.duration_s)
        else:
            failures.append(f"rep[{i - warmup}]: {result.reason}")
    return durations, failures


# --------------------------------------------------------------------------- #
# Pure core: per-surface result + report assembly                              #
# --------------------------------------------------------------------------- #


def build_surface_measured(
    surface: str,
    durations: list[float],
    *,
    requested: int,
    warmup: int,
    verify_ms: float | None,
    failures: list[str],
) -> dict[str, Any]:
    """Assemble a 'measured' surface block from non-empty durations (pure)."""
    block: dict[str, Any] = {
        "surface": surface,
        "status": "measured",
        "requested_reps": requested,
        "warmup_reps": warmup,
        "kept_reps": len(durations),
        # ``prove`` is the full per-exec WALL time (process spawn + stdin parse +
        # ELF/proving-system load + STARK prove() + receipt serialize + stdout
        # write), NOT the isolated prove() call — see module docstring item 1 and
        # the env ``exec_overhead_s`` floor for the proving-vs-overhead split.
        "prove": summarize_stats(durations),
        # Single representative verify sample (n=1, NOT a distribution); see the
        # module docstring item 4. ``None`` only if the surface cannot verify.
        "verify_ms_single": verify_ms,
    }
    if failures:
        block["partial_failures"] = failures
    return block


def build_surface_unmeasured(surface: str, reason: str) -> dict[str, Any]:
    """Assemble an 'unmeasured' surface block (pure). NO fabricated number."""
    return {"surface": surface, "status": "unmeasured", "reason": reason}


def build_report(
    *,
    environment: dict[str, Any],
    build_cost_s: float | None,
    build_status: str,
    build_reason: str,
    surfaces: list[dict[str, Any]],
    reps: int,
    warmup: int,
    exec_overhead_s: float | None = None,
) -> dict[str, Any]:
    """Assemble the top-level report object (pure).

    ``exec_overhead_s`` is the measured wall-time floor of a single fast,
    non-proving CLI exec (process spawn + stdin parse + reject). It is reported
    so a reader can see how much of each ``prove`` figure is fixed exec overhead
    vs. actual STARK proving; it is NEVER subtracted from the prove number.
    """
    measured = [s for s in surfaces if s.get("status") == "measured"]
    return {
        "schema": SCHEMA,
        "dev_mode": False,
        "reps": reps,
        "warmup": warmup,
        "build": {
            "status": build_status,
            "cost_s": build_cost_s,
            "reason": build_reason,
            "counted_as_prove_time": False,
        },
        "exec_overhead_s": exec_overhead_s,
        "environment": environment,
        "surface_count": len(surfaces),
        "measured_count": len(measured),
        "all_measured": len(measured) == len(surfaces) and len(surfaces) > 0,
        "surfaces": surfaces,
    }


# --------------------------------------------------------------------------- #
# Pure core: markdown rendering                                                #
# --------------------------------------------------------------------------- #


def _fmt_s(value: float) -> str:
    return f"{value:.3f}"


def _opt_s(value: Any) -> str:
    """Format an optional numeric seconds value, ``n/a`` when absent."""
    return _fmt_s(value) if isinstance(value, (int, float)) else "n/a"


def _markdown_preamble(report: dict[str, Any]) -> list[str]:
    """Header + environment bullet list (pure)."""
    env = report.get("environment", {})
    build = report.get("build", {})
    return [
        "# RISC0 prove-time benchmark",
        "",
        f"- dev_mode: `{report.get('dev_mode')}`",
        f"- reps: {report.get('reps')} (warmup {report.get('warmup')}; reps timed AFTER warmup)",
        f"- cpu: {env.get('cpu_model', '?')} x{env.get('cpu_count', '?')}",
        f"- risc0_version: {env.get('risc0_version', '?')}",
        f"- prover_backend: {env.get('prover_backend', '?')}; "
        f"rayon_num_threads: {env.get('rayon_num_threads', '?')}; "
        f"load_avg: {env.get('load_average', '?')}",
        f"- git_commit: {env.get('git_commit', '?')}",
        f"- build_cost_s: {_opt_s(build.get('cost_s'))} "
        f"(status {build.get('status')}; NOT counted as prove time)",
        f"- exec_overhead_s: {_opt_s(report.get('exec_overhead_s'))} "
        "(fixed per-exec floor; included in prove, never subtracted)",
        "",
        "_prove columns are full CLI exec WALL seconds (incl. fixed overhead), "
        "not isolated prove(); at small N the p99 column equals the observed max, "
        "not a tail estimate. verify is a single n=1 sample, not a distribution._",
        "",
    ]


def _markdown_measured_row(surface: dict[str, Any]) -> str:
    """One table row for a measured surface (pure)."""
    prove = surface.get("prove", {})
    verify_str = _opt_ms(surface.get("verify_ms_single"))
    p99 = _fmt_s(prove.get("p99_s", 0.0))
    if prove.get("p99_is_max"):
        p99 += "*"
    return (
        f"| {surface.get('surface', '?')} | measured | {prove.get('n', '?')} | "
        f"{_fmt_s(prove.get('min_s', 0.0))} | {_fmt_s(prove.get('median_s', 0.0))} | "
        f"{_fmt_s(prove.get('mean_s', 0.0))} | {p99} | "
        f"{_fmt_s(prove.get('stdev_s', 0.0))} | {verify_str} |"
    )


def _opt_ms(value: Any) -> str:
    return f"{value:.1f}" if isinstance(value, (int, float)) else "n/a"


def _sanitize_reason(reason: Any) -> str:
    """First line of a reason, pipe-safe and length-capped for a table/footnote."""
    lines = str(reason).replace("|", "/").splitlines()
    return lines[0][:120] if lines else ""


def render_markdown(report: dict[str, Any]) -> str:
    """Render a human markdown table from a report (pure).

    Unmeasured surfaces show ``-`` in every numeric column and a footnote
    reference; their reason is listed below the table (NOT overloaded into the
    verify column, which is reserved for verify times).
    """
    lines: list[str] = list(_markdown_preamble(report))
    lines.append(
        "| surface | status | reps | min_s | median_s | mean_s | p99_s | stdev_s | verify_ms_single |"
    )
    lines.append("|---|---|---|---|---|---|---|---|---|")
    footnotes: list[str] = []
    for surface in report.get("surfaces", []):
        name = surface.get("surface", "?")
        if surface.get("status") == "measured":
            lines.append(_markdown_measured_row(surface))
        else:
            footnotes.append(f"- `{name}`: {_sanitize_reason(surface.get('reason', ''))}")
            lines.append(f"| {name} | unmeasured | - | - | - | - | - | - | - |")
    lines.append("")
    if any(
        s.get("status") == "measured" and s.get("prove", {}).get("p99_is_max")
        for s in report.get("surfaces", [])
    ):
        lines.append("\\* p99 == observed max at this N (nearest-rank); not a tail estimate.")
        lines.append("")
    if footnotes:
        lines.append("Unmeasured surfaces:")
        lines.extend(footnotes)
        lines.append("")
    return "\n".join(lines)


# --------------------------------------------------------------------------- #
# Shell: environment capture                                                   #
# --------------------------------------------------------------------------- #


def _read_cpu_model() -> str:
    try:
        text = Path("/proc/cpuinfo").read_text(encoding="utf-8", errors="replace")
    except OSError:
        return "unknown"
    for line in text.splitlines():
        if line.lower().startswith("model name"):
            _, _, value = line.partition(":")
            return value.strip() or "unknown"
    return "unknown"


def _read_risc0_version(lock_path: Path) -> str:
    """Resolve the actual risc0-zkvm version from Cargo.lock (not Cargo.toml)."""
    try:
        text = lock_path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return "unknown"
    match = re.search(r'name = "risc0-zkvm"\nversion = "([^"]+)"', text)
    return match.group(1) if match else "unknown"


def _git_commit(repo: Path) -> str:
    try:
        out = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=repo,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            text=True,
            timeout=20,
            check=False,
        )
    except (OSError, subprocess.SubprocessError):
        return "unknown"
    return out.stdout.strip() if out.returncode == 0 else "unknown"


def _load_average() -> list[float] | None:
    """1-/5-/15-min load average, or None where the OS does not expose it."""
    try:
        one, five, fifteen = os.getloadavg()
    except (OSError, AttributeError):
        return None
    return [round(one, 2), round(five, 2), round(fifteen, 2)]


def capture_environment(repo: Path) -> dict[str, Any]:
    """Record CPU, resolved RISC0 version, commit, and the load-affecting knobs.

    The prover backend and thread count materially change prove time; capturing
    them (plus the current load average) keeps a recorded figure comparable
    across runs and flags when two runs are not apples-to-apples.
    """
    return {
        "cpu_model": _read_cpu_model(),
        "cpu_count": os.cpu_count(),
        "risc0_version": _read_risc0_version(repo / CLI_LOCK_REL),
        "git_commit": _git_commit(repo),
        "prover_backend": os.environ.get("RISC0_PROVER", "local/default"),
        "rayon_num_threads": os.environ.get("RAYON_NUM_THREADS", "unset"),
        "load_average": _load_average(),
    }


def proving_env() -> dict[str, str]:
    """Pinned environment held constant across build + every prove/verify.

    RISC0_FORCE_BUILD=1 forces a real embedded guest ELF; RISC0_DEV_MODE=0 pins
    real proving; RISC0_PROVER is left to local/default unless explicitly set.
    """
    env = os.environ.copy()
    env["RISC0_FORCE_BUILD"] = "1"
    env["RISC0_DEV_MODE"] = "0"
    return env


# --------------------------------------------------------------------------- #
# Shell: build runner (injected; default does a real cargo build)             #
# --------------------------------------------------------------------------- #


@dataclass
class BuildOutcome:
    ok: bool
    cost_s: float | None
    reason: str
    cli_bin: Path | None = None


def real_build(repo: Path, target_dir: Path, timeout: int) -> BuildOutcome:
    """Build the CLI once; return the prebuilt binary path and the build cost."""
    env = proving_env()
    env["CARGO_TARGET_DIR"] = str(target_dir)
    start = time.perf_counter()
    try:
        proc = subprocess.run(
            [
                "cargo",
                "build",
                "--release",
                "--manifest-path",
                str(repo / CLI_MANIFEST_REL),
                "-q",
                "-p",
                CLI_PACKAGE,
            ],
            cwd=repo,
            env=env,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=timeout,
            check=False,
        )
    except FileNotFoundError:
        return BuildOutcome(False, None, "cargo not found (toolchain absent)")
    except subprocess.TimeoutExpired:
        return BuildOutcome(False, None, f"build timed out after {timeout}s")
    cost = time.perf_counter() - start
    if proc.returncode != 0:
        return BuildOutcome(False, None, f"build failed exit={proc.returncode}: {proc.stderr[-600:].strip()}")
    cli_bin = target_dir / CLI_BIN_REL
    if not cli_bin.exists():
        return BuildOutcome(False, None, f"built but missing binary: {cli_bin}")
    return BuildOutcome(True, cost, "", cli_bin)


# --------------------------------------------------------------------------- #
# Shell: prove / verify exec against the prebuilt binary                       #
# --------------------------------------------------------------------------- #


def _exec_cli(
    *,
    cli_bin: Path,
    repo: Path,
    target_dir: Path,
    request: dict[str, Any],
    timeout: int,
) -> tuple[int, str, str, float]:
    """Exec the prebuilt CLI with request JSON on stdin; return (rc, out, err, secs)."""
    env = proving_env()
    env["CARGO_TARGET_DIR"] = str(target_dir)
    payload = json.dumps(request, separators=(",", ":"))
    start = time.perf_counter()
    proc = subprocess.run(
        [str(cli_bin)],
        cwd=repo,
        env=env,
        input=payload,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=timeout,
        check=False,
    )
    elapsed = time.perf_counter() - start
    return proc.returncode, proc.stdout, proc.stderr, elapsed


def classify_prove_output(rc: int, out: str, err: str, secs: float) -> SampleRun:
    """Pure fail-closed classifier for one prove invocation.

    A run counts ONLY if rc==0 AND stdout parses as JSON AND has a non-empty
    base64 ``proof`` field. Any other outcome (including rc==0 with an empty or
    missing proof — what a truncated output looks like) is a failure with NO
    duration, so a fast crash can never masquerade as throughput.

    IMPORTANT (defense boundary): the non-empty-``proof`` check does NOT detect
    a RISC0 dev-mode FakeReceipt, which still serializes to a non-empty base64
    proof string AND still "verifies" successfully — so neither this check nor
    the verify gate can catch it. The SOLE defense against a fast non-proving
    dev fake being recorded as a real prove time is the ``RISC0_DEV_MODE`` guard:
    ``main()`` refuses when it is truthy and ``proving_env()`` pins it to ``0``
    for build + every prove/verify exec. The representative verify gate (see
    ``measure_surface``) defends a DIFFERENT failure mode — a receipt that does
    NOT verify (corrupt / wrong bindings) downgrades the whole surface to
    ``unmeasured`` rather than reporting its time; it does not and cannot detect
    a dev fake, which verifies fine.
    """
    if rc != 0:
        return SampleRun(0.0, False, f"prove exit={rc}: {err[-300:].strip()}")
    try:
        parsed = json.loads(out)
    except json.JSONDecodeError as exc:
        return SampleRun(0.0, False, f"prove returned invalid JSON: {exc}")
    proof_b64 = parsed.get("proof") if isinstance(parsed, dict) else None
    if not isinstance(proof_b64, str) or not proof_b64:
        return SampleRun(0.0, False, "prove returned empty/missing proof field")
    return SampleRun(secs, True)


def make_prove_runner(
    *,
    cli_bin: Path,
    repo: Path,
    target_dir: Path,
    request: dict[str, Any],
    timeout: int,
) -> Callable[[int], SampleRun]:
    """Build an injectable single-prove runner bound to a fixed request."""

    def run_one(_i: int) -> SampleRun:
        try:
            rc, out, err, secs = _exec_cli(
                cli_bin=cli_bin,
                repo=repo,
                target_dir=target_dir,
                request=request,
                timeout=timeout,
            )
        except subprocess.TimeoutExpired:
            return SampleRun(0.0, False, f"prove timed out after {timeout}s")
        except OSError as exc:  # exec failure after build (binary gone/perm/etc.)
            return SampleRun(0.0, False, f"prove exec failed: {exc}")
        return classify_prove_output(rc, out, err, secs)

    return run_one


def classify_verify_output(rc: int, out: str, err: str, secs: float) -> tuple[float | None, str]:
    """Pure fail-closed classifier for one verify invocation.

    Returns ``(ms, "")`` only on rc==0 with parsed ``ok: true``; otherwise
    ``(None, reason)`` so a rejected/garbled verify never yields a misleading ms.
    """
    if rc != 0:
        return None, f"verify exit={rc}: {err[-300:].strip()}"
    try:
        parsed = json.loads(out)
    except json.JSONDecodeError as exc:
        return None, f"verify returned invalid JSON: {exc}"
    if not isinstance(parsed, dict) or parsed.get("ok") is not True:
        return None, f"verify rejected: {parsed}"
    return secs * 1000.0, ""


def time_verify(
    *,
    cli_bin: Path,
    repo: Path,
    target_dir: Path,
    verify_request: dict[str, Any],
    timeout: int,
) -> tuple[float | None, str]:
    """Time one receipt.verify (ms). Returns (ms, "") on accept; (None, reason) otherwise."""
    try:
        rc, out, err, secs = _exec_cli(
            cli_bin=cli_bin,
            repo=repo,
            target_dir=target_dir,
            request=verify_request,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return None, f"verify timed out after {timeout}s"
    except OSError as exc:  # exec failure after build => unmeasured, never a crash
        return None, f"verify exec failed: {exc}"
    return classify_verify_output(rc, out, err, secs)


# Request the CLI rejects immediately WITHOUT proving (unknown schema => fast
# exit 2). Times the fixed per-exec floor: fork/exec + stdin parse + reject.
_OVERHEAD_PROBE_REQUEST: dict[str, Any] = {"schema": "tau_state_proof_noop_overhead_probe"}


def measure_exec_overhead(
    *,
    cli_bin: Path,
    repo: Path,
    target_dir: Path,
    timeout: int,
) -> float | None:
    """Wall-time floor of one fast NON-PROVING CLI exec, or None if unmeasurable.

    Characterizes the fixed per-exec overhead (process spawn + stdin parse +
    reject) bundled into every ``prove`` figure, so a reader can see the
    proving-vs-overhead split. Never subtracted from the prove number.
    """
    try:
        _rc, _out, _err, secs = _exec_cli(
            cli_bin=cli_bin,
            repo=repo,
            target_dir=target_dir,
            request=_OVERHEAD_PROBE_REQUEST,
            timeout=timeout,
        )
    except (subprocess.TimeoutExpired, OSError):
        return None
    return secs


# --------------------------------------------------------------------------- #
# Shell: deterministic per-surface request builders                            #
# --------------------------------------------------------------------------- #


@dataclass
class SurfacePlan:
    """A fixed (generate, verify) request pair for one surface, or an import error."""

    generate: dict[str, Any] | None = None
    verify: dict[str, Any] | None = None
    error: str = ""
    extra: dict[str, Any] = field(default_factory=dict)


def _spot_plan() -> SurfacePlan:
    """Spot 'empty' transition: no txs, pre_hash == post_hash. Inlined (no heavy imports)."""
    import hashlib

    def canonical(value: Any) -> bytes:
        return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")

    empty_hash = hashlib.sha256(canonical(SPOT_EMPTY_SNAPSHOT)).hexdigest()
    app_state_pre = canonical(SPOT_EMPTY_SNAPSHOT).decode("utf-8")
    generate = {
        "schema": "tau_state_proof_request",
        "schema_version": 1,
        "state_hash": SPOT_STATE_HASH,
        "block": {"header": {"timestamp": 1}, "transactions": []},
        "tau_state": {"app_hash": empty_hash},
        "context": {
            "app_state_pre": app_state_pre,
            "app_hash_pre": empty_hash,
            "chain_balances_post": {},
        },
    }
    verify = {
        "schema": "tau_state_proof_verify",
        "schema_version": 1,
        "state_hash": SPOT_STATE_HASH,
        "proof": None,  # filled in with the generated proof object before verify
        "block": {"header": {"timestamp": 1}, "transactions": []},
        "tau_state": {"app_hash": empty_hash},
        "context": {"app_hash_pre": empty_hash, "block_timestamp": 1},
    }
    return SurfacePlan(generate=generate, verify=verify)


def _perps_np_plan(repo: Path) -> SurfacePlan:
    """Perps-NP 'four_wallet' settle+match (>=4 participants, net_position_base==0)."""
    try:
        smoke = _import_smoke_module(repo, "zeno_ledger_perp_np_risc0_real_proof_smoke")
    except Exception as exc:  # noqa: BLE001 - import failure => unmeasured surface
        return SurfacePlan(error=f"perps_np import failed: {exc}")
    try:
        case_input = smoke._cases()["four_wallet"]["input"]
        generate = smoke._current_generate_request("four_wallet", case_input)
    except Exception as exc:  # noqa: BLE001
        return SurfacePlan(error=f"perps_np request build failed: {exc}")
    # Verify uses the strict perps-np verifier, built from the proof's own meta
    # at run time, so we stash the actions + the smoke module's verify builder.
    return SurfacePlan(
        generate=generate,
        extra={
            "verify_builder": "perps_np",
            "actions": json.loads(json.dumps(generate["actions"])),
        },
    )


def _zusd_plan(repo: Path) -> SurfacePlan:
    """zUSD 'mint' deposit+mint transition (minted_zusd_e8 > 0)."""
    try:
        smoke = _import_smoke_module(repo, "zeno_ledger_zusd_risc0_real_proof_smoke")
    except Exception as exc:  # noqa: BLE001
        return SurfacePlan(error=f"zusd import failed: {exc}")
    try:
        case_input = smoke._cases()["mint"]["input"]
        generate = smoke._generate_request("mint", case_input)
    except Exception as exc:  # noqa: BLE001
        return SurfacePlan(error=f"zusd request build failed: {exc}")
    return SurfacePlan(
        generate=generate,
        extra={"verify_builder": "zusd", "operation": json.loads(json.dumps(generate["operation"]))},
    )


def _clob_plan(repo: Path) -> SurfacePlan:
    """CLOB 'single_full_fill' from the deterministic fixture (accepted == true)."""
    fixture_path = repo / "zk/state_proof_risc0/shared/src/clob_match_cases_v1.json"
    try:
        fixture = json.loads(fixture_path.read_text(encoding="utf-8"))
    except OSError as exc:
        return SurfacePlan(error=f"clob fixture unreadable: {exc}")
    case = next(
        (c for c in fixture.get("cases", []) if c.get("name") == "single_full_fill"),
        None,
    )
    if case is None or not case.get("result", {}).get("accepted"):
        return SurfacePlan(error="clob fixture missing accepted 'single_full_fill' case")
    post_book_root = case["result"]["post_book_root"]
    pre_book = {
        "base_asset": case["base_asset"],
        "quote_asset": case["quote_asset"],
        "orders": case["orders"],
    }
    generate = {
        "schema": "tau_state_proof_request",
        "schema_version": 1,
        "proof_type": "risc0.zenodex_clob_transition.v1",
        "state_hash": CLOB_STATE_HASH,
        "chain_id": CLOB_CHAIN_ID,
        "pre_book": pre_book,
        "taker": case["taker"],
        "context": {"chain_id": CLOB_CHAIN_ID},
        "expected_post_app_hash": post_book_root,
        "tau_state": {"app_hash": post_book_root},
    }
    return SurfacePlan(
        generate=generate,
        extra={"verify_builder": "clob", "taker": case["taker"], "post_book_root": post_book_root},
    )


def build_surface_plans(repo: Path) -> dict[str, SurfacePlan]:
    """Build all four deterministic request plans. Pure w.r.t. timing (no proving)."""
    return {
        "spot": _spot_plan(),
        "perps_np": _perps_np_plan(repo),
        "zusd": _zusd_plan(repo),
        "clob": _clob_plan(repo),
    }


def surface_supports_verify(surface: str, plan: SurfacePlan) -> bool:
    """Pure predicate: can a verify request be assembled for this surface/plan?

    Load-bearing for the verify FAIL-CLOSED gate (see ``measure_surface``): a
    surface that supports verify MUST verify to stay ``measured``; a surface
    that cannot assemble a verify request at all skips verify (informational).
    Mirrors the surface branches in ``build_verify_request``: spot is gated by a
    static verify template; the typed surfaces are gated by their ``extra``
    verify-builder tag.
    """
    if surface == "spot":
        return plan.verify is not None
    return bool(plan.extra.get("verify_builder"))


# --------------------------------------------------------------------------- #
# Shell: build a verify request from a generated proof + plan extras           #
# --------------------------------------------------------------------------- #


def build_verify_request(
    surface: str,
    plan: SurfacePlan,
    proof: dict[str, Any],
) -> dict[str, Any] | None:
    """Construct the verify request for a surface from its generated proof.

    Returns None if a verify request cannot be assembled (verify then skipped,
    but prove timing is still reported).
    """
    if surface == "spot":
        if plan.verify is None:
            return None
        request = json.loads(json.dumps(plan.verify))
        request["proof"] = proof
        return request
    meta = proof.get("meta")
    if not isinstance(meta, dict):
        return None
    if surface == "zusd":
        operation = plan.extra.get("operation")
        keys = (
            "chain_id",
            "pre_app_hash",
            "post_app_hash",
            "operation_hash",
            "state_delta_hash",
            "oracle_binding_hash",
            "participant_set_hash",
            "zusd_balance_root_hash",
            "zusd_vault_root_hash",
        )
        if operation is None or any(k not in meta for k in keys):
            return None
        context = {
            "chain_id": meta["chain_id"],
            "app_hash_pre": meta["pre_app_hash"],
            "operation_hash": meta["operation_hash"],
            "state_delta_hash": meta["state_delta_hash"],
            "oracle_binding_hash": meta["oracle_binding_hash"],
            "participant_set_hash": meta["participant_set_hash"],
            "zusd_balance_root_hash": meta["zusd_balance_root_hash"],
            "zusd_vault_root_hash": meta["zusd_vault_root_hash"],
        }
        return {
            "schema": "tau_state_proof_verify",
            "schema_version": 1,
            "state_hash": proof["state_hash"],
            "chain_id": meta["chain_id"],
            "proof": proof,
            "tau_state": {"app_hash": meta["post_app_hash"]},
            "context": context,
            "operation": operation,
        }
    if surface == "perps_np":
        actions = plan.extra.get("actions")
        keys = (
            "chain_id",
            "pre_app_hash",
            "post_app_hash",
            "operation_hash",
            "state_delta_hash",
            "oracle_binding_hash",
            "collateral_binding_hash",
            "participant_set_hash",
            "receipt_root",
        )
        if actions is None or any(k not in meta for k in keys):
            return None
        context = {
            "chain_id": meta["chain_id"],
            "app_hash_pre": meta["pre_app_hash"],
            "operation_hash": meta["operation_hash"],
            "state_delta_hash": meta["state_delta_hash"],
            "oracle_binding_hash": meta["oracle_binding_hash"],
            "collateral_binding_hash": meta["collateral_binding_hash"],
            "participant_set_hash": meta["participant_set_hash"],
            "receipt_root": meta["receipt_root"],
        }
        return {
            "schema": "tau_state_proof_verify",
            "schema_version": 1,
            "state_hash": proof["state_hash"],
            "chain_id": meta["chain_id"],
            "proof": proof,
            "tau_state": {"app_hash": meta["post_app_hash"]},
            "context": context,
            "actions": actions,
        }
    if surface == "clob":
        taker = plan.extra.get("taker")
        post_book_root = plan.extra.get("post_book_root")
        if taker is None or post_book_root is None or plan.generate is None:
            return None
        # Minimal CLOB verify: bind state_hash + tau_state + closed context.
        context = {"chain_id": CLOB_CHAIN_ID}
        for key in ("pre_book_root", "operation_hash", "state_delta_hash", "event_log_root", "matching_rule_hash", "fee_rule_hash"):
            if key in meta:
                context[key] = meta[key]
        return {
            "schema": "tau_state_proof_verify",
            "schema_version": 1,
            "state_hash": proof["state_hash"],
            "chain_id": CLOB_CHAIN_ID,
            "proof": proof,
            "pre_book": plan.generate["pre_book"],
            "taker": taker,
            "tau_state": {"app_hash": post_book_root},
            "context": context,
        }
    return None


# --------------------------------------------------------------------------- #
# Shell: measure a single surface end to end                                   #
# --------------------------------------------------------------------------- #


def measure_surface(
    surface: str,
    plan: SurfacePlan,
    *,
    cli_bin: Path,
    repo: Path,
    target_dir: Path,
    reps: int,
    warmup: int,
    prove_timeout: int,
    verify_timeout: int,
) -> dict[str, Any]:
    """Measure one surface: N timed proves + one representative verify.

    Fail-closed on BOTH dimensions: if no prove rep succeeds the surface is
    unmeasured; if the surface supports verify (can assemble a verify request)
    but the representative verify does not return ``ok``, the surface is ALSO
    downgraded to unmeasured with NO prove number — a proof that does not verify
    is not a measurement. See module docstring item 6.
    """
    if plan.error:
        return build_surface_unmeasured(surface, plan.error)
    if plan.generate is None:
        return build_surface_unmeasured(surface, "no generate request")

    log(f"[{surface}] proving {reps} reps (warmup {warmup}) ...")
    run_one = make_prove_runner(
        cli_bin=cli_bin,
        repo=repo,
        target_dir=target_dir,
        request=plan.generate,
        timeout=prove_timeout,
    )
    durations, failures = collect_samples(run_one, reps, warmup=warmup)

    # Representative verify (n=1) only if we have something to report AND the
    # surface can build a verify request. The actual measured/unmeasured DECISION
    # lives in the pure ``finalize_surface`` below so it is unit-testable.
    supports_verify = surface_supports_verify(surface, plan)
    verify_ms: float | None = None
    verify_reason = ""
    if durations and supports_verify:
        verify_ms, verify_reason = _representative_verify(
            surface,
            plan,
            cli_bin=cli_bin,
            repo=repo,
            target_dir=target_dir,
            prove_timeout=prove_timeout,
            verify_timeout=verify_timeout,
        )

    block = finalize_surface(
        surface,
        durations,
        requested=reps,
        warmup=warmup,
        supports_verify=supports_verify,
        verify_ms=verify_ms,
        verify_reason=verify_reason,
        failures=failures,
    )
    if block["status"] == "measured":
        log(f"[{surface}] kept {len(durations)}/{reps} reps; "
            f"median {statistics.median(durations):.3f}s")
    else:
        log(f"[{surface}] unmeasured: {block['reason']}")
    return block


def finalize_surface(
    surface: str,
    durations: list[float],
    *,
    requested: int,
    warmup: int,
    supports_verify: bool,
    verify_ms: float | None,
    verify_reason: str,
    failures: list[str],
) -> dict[str, Any]:
    """Pure fail-closed decision: turn prove durations + a verify outcome into a
    surface block. This is the load-bearing measured/unmeasured gate.

    Rules (both dimensions fail-closed):
    - no successful prove rep => ``unmeasured`` (no fabricated number);
    - surface supports verify but the representative verify did not return a ms
      (``verify_ms is None``) => ``unmeasured`` with the verify reason and NO
      prove number — a proof that does not verify is not a measurement;
    - surface cannot assemble a verify request (``supports_verify`` False) =>
      verify is informational and never gates (none of the live surfaces).
    """
    if not durations:
        reason = "no successful prove repetitions"
        if failures:
            reason += "; " + failures[0]
        return build_surface_unmeasured(surface, reason)
    if failures:
        # Fail-closed (Codex review HIGH): a measurement is clean ONLY if every timed
        # rep succeeded. A failed/timed-out prove rep coexisting with reported stats
        # would let a partial run masquerade as a real measurement. Downgrade to
        # unmeasured with the failure reason -- never report stats over fewer than N.
        reason = (
            f"{len(failures)} of {requested} prove reps failed; a clean measurement "
            f"requires all reps to succeed: {failures[0]}"
        )
        return build_surface_unmeasured(surface, reason)
    if supports_verify and verify_ms is None:
        return build_surface_unmeasured(
            surface, f"verify failed: {verify_reason or 'verify did not return ok'}"
        )
    return build_surface_measured(
        surface,
        durations,
        requested=requested,
        warmup=warmup,
        verify_ms=verify_ms,
        failures=failures,
    )


def _representative_verify(
    surface: str,
    plan: SurfacePlan,
    *,
    cli_bin: Path,
    repo: Path,
    target_dir: Path,
    prove_timeout: int,
    verify_timeout: int,
) -> tuple[float | None, str]:
    """Generate one fresh binding proof and time a single verify against it.

    Returns ``(ms, "")`` only when a fresh proof regenerates, a verify request
    assembles, and that verify returns ``ok``; otherwise ``(None, reason)`` so
    the caller can fail the surface closed.
    """
    if plan.generate is None:
        return None, "no generate request"
    fresh = run_one_proof(
        cli_bin=cli_bin, repo=repo, target_dir=target_dir, request=plan.generate, timeout=prove_timeout
    )
    if fresh is None:
        return None, "could not regenerate a binding proof for verify"
    verify_request = build_verify_request(surface, plan, fresh)
    if verify_request is None:
        return None, "could not assemble verify request from proof meta"
    return time_verify(
        cli_bin=cli_bin,
        repo=repo,
        target_dir=target_dir,
        verify_request=verify_request,
        timeout=verify_timeout,
    )


def run_one_proof(
    *,
    cli_bin: Path,
    repo: Path,
    target_dir: Path,
    request: dict[str, Any],
    timeout: int,
) -> dict[str, Any] | None:
    """Produce one proof object (for verify binding); None on any failure."""
    try:
        rc, out, _err, _secs = _exec_cli(
            cli_bin=cli_bin, repo=repo, target_dir=target_dir, request=request, timeout=timeout
        )
    except (subprocess.TimeoutExpired, OSError):
        return None
    if rc != 0:
        return None
    try:
        parsed = json.loads(out)
    except json.JSONDecodeError:
        return None
    return parsed if isinstance(parsed, dict) else None


# --------------------------------------------------------------------------- #
# Orchestration (shell)                                                        #
# --------------------------------------------------------------------------- #


def run_benchmark(args: argparse.Namespace) -> dict[str, Any]:
    repo = args.repo.resolve()
    target_dir = args.target_dir.resolve()
    target_dir.mkdir(parents=True, exist_ok=True)

    environment = capture_environment(repo)
    log(f"environment: cpu={environment['cpu_model']} x{environment['cpu_count']}; "
        f"risc0={environment['risc0_version']}; commit={environment['git_commit'][:12]}")
    log("building CLI once (build cost recorded separately) ...")

    build = real_build(repo, target_dir, args.build_timeout)
    if not build.ok or build.cli_bin is None:
        log(f"build unmeasured: {build.reason}")
        surfaces = [build_surface_unmeasured(s, "build unavailable") for s in SURFACES]
        return build_report(
            environment=environment,
            build_cost_s=None,
            build_status="failed",
            build_reason=build.reason,
            surfaces=surfaces,
            reps=args.reps,
            warmup=args.warmup,
        )
    log(f"build ok in {build.cost_s:.1f}s")

    exec_overhead_s = measure_exec_overhead(
        cli_bin=build.cli_bin,
        repo=repo,
        target_dir=target_dir,
        timeout=args.verify_timeout,
    )
    log(f"exec overhead floor: {_opt_s(exec_overhead_s)}s (non-proving exec; not subtracted)")

    plans = build_surface_plans(repo)
    selected = SURFACES if args.surface == "all" else (args.surface,)
    measured_surfaces: list[dict[str, Any]] = []
    for name in selected:
        measured_surfaces.append(
            measure_surface(
                name,
                plans[name],
                cli_bin=build.cli_bin,
                repo=repo,
                target_dir=target_dir,
                reps=args.reps,
                warmup=args.warmup,
                prove_timeout=args.prove_timeout,
                verify_timeout=args.verify_timeout,
            )
        )

    return build_report(
        environment=environment,
        build_cost_s=build.cost_s,
        build_status="ok",
        build_reason="",
        surfaces=measured_surfaces,
        reps=args.reps,
        warmup=args.warmup,
        exec_overhead_s=exec_overhead_s,
    )


def emit(report: dict[str, Any], args: argparse.Namespace) -> None:
    """Write JSON to stdout; optional markdown to stderr; optional --out file."""
    if args.markdown:
        log("")
        log(render_markdown(report))
    if args.out is not None:
        out_path = args.out.resolve()
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(json.dumps(report, sort_keys=True, indent=2) + "\n", encoding="utf-8")
        if args.markdown:
            md_path = out_path.with_suffix(".md")
            md_path.write_text(render_markdown(report) + "\n", encoding="utf-8")
        log(f"results written to {out_path}")
    print(json.dumps(report, sort_keys=True, indent=2))


# --------------------------------------------------------------------------- #
# Self-test: validate harness LOGIC with NO real STARK, in < 5s                #
# --------------------------------------------------------------------------- #


def _selftest_assert(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def run_self_test() -> int:
    """Validate timing capture, stats, JSON+markdown shape, dev-mode guard, the
    verify-gate fail-closed decision, and fail-closed-on-build-failure WITHOUT
    running a real STARK. Returns 0 on pass."""
    log("self-test: starting (no real STARK)")

    # 1. dev-mode predicate (the load-bearing guard).
    for truthy in ("1", "true", "TRUE", "Yes", "on"):
        _selftest_assert(dev_mode_is_truthy(truthy), f"dev_mode should be truthy for {truthy!r}")
    for falsy in ("0", "false", "", "  ", "no", None):
        _selftest_assert(not dev_mode_is_truthy(falsy), f"dev_mode should be falsy for {falsy!r}")

    # 2. percentile (nearest-rank) and stats against hand-computed values.
    _selftest_assert(percentile([1.0, 2.0, 3.0, 4.0, 5.0], 99.0) == 5.0, "p99 of 5 -> max")
    _selftest_assert(percentile([10.0], 99.0) == 10.0, "p99 of singleton -> itself")
    _selftest_assert(percentile([1.0, 2.0, 3.0, 4.0], 50.0) == 2.0, "p50 nearest-rank")
    stats = summarize_stats([2.0, 4.0, 4.0, 4.0, 5.0, 5.0, 7.0, 9.0])
    _selftest_assert(stats["min_s"] == 2.0, "min")
    _selftest_assert(stats["median_s"] == 4.5, "median")
    _selftest_assert(abs(stats["mean_s"] - 5.0) < 1e-9, "mean")
    # sample stdev: sum_sq_dev = 32, variance = 32/(8-1), sqrt = 2.13808993...
    _selftest_assert(abs(stats["stdev_s"] - 2.138089935299395) < 1e-9, "stdev (sample)")
    _selftest_assert(stats["p99_s"] == 9.0, "p99 -> max")
    _selftest_assert(stats["p99_is_max"] is True, "p99_is_max flag set at small N")
    single = summarize_stats([3.0])
    _selftest_assert(single["stdev_s"] == 0.0, "stdev of singleton is 0")
    _selftest_assert(single["p99_is_max"] is True, "p99_is_max for singleton")

    # 3. timing capture: real perf_counter over a tiny sleep, via collect_samples.
    def sleepy_run(_i: int) -> SampleRun:
        start = time.perf_counter()
        time.sleep(0.002)
        return SampleRun(time.perf_counter() - start, True)

    durations, failures = collect_samples(sleepy_run, 3, warmup=1)
    _selftest_assert(len(durations) == 3, "collect_samples keeps n reps after warmup")
    _selftest_assert(not failures, "no failures expected for sleepy runner")
    _selftest_assert(all(d >= 0.001 for d in durations), "captured durations are real")

    # 4a. fail-closed PROVE classifier — the load-bearing gate. Drive it directly
    #     with synthetic CLI outputs so every branch is exercised (no STARK).
    ok_run = classify_prove_output(0, '{"proof":"AAAA","schema":"tau_state_proof"}', "", 0.5)
    _selftest_assert(ok_run.ok and ok_run.duration_s == 0.5, "prove ok: rc0+proof -> counted")
    _selftest_assert(not classify_prove_output(1, "", "boom", 0.0).ok, "prove fail: rc!=0")
    _selftest_assert(not classify_prove_output(0, "not json", "", 0.0).ok, "prove fail: invalid JSON")
    # The critical case: rc==0 but NO proof (dev-fake / truncated) must NOT count.
    empty_proof = classify_prove_output(0, '{"schema":"tau_state_proof"}', "", 0.001)
    _selftest_assert(not empty_proof.ok, "prove fail: rc0 but missing proof field")
    _selftest_assert(empty_proof.duration_s == 0.0, "fast fake contributes NO duration")
    _selftest_assert(not classify_prove_output(0, '{"proof":""}', "", 0.0).ok, "prove fail: rc0 empty proof string")

    # 4b. fail-closed VERIFY classifier.
    ms, reason = classify_verify_output(0, '{"ok":true}', "", 0.012)
    _selftest_assert(ms is not None and abs(ms - 12.0) < 1e-6 and reason == "", "verify ok -> ms")
    ms_bad, reason_bad = classify_verify_output(0, '{"ok":false,"error":"x"}', "", 0.5)
    _selftest_assert(ms_bad is None and bool(reason_bad), "verify reject -> None + reason")
    _selftest_assert(classify_verify_output(2, "", "err", 0.0)[0] is None, "verify rc!=0 -> None")
    _selftest_assert(classify_verify_output(0, "garbage", "", 0.0)[0] is None, "verify invalid JSON -> None")

    # 4c. fail-closed: a runner that errors yields NO duration and an unmeasured surface.
    def broken_run(_i: int) -> SampleRun:
        return SampleRun(0.0, False, "simulated prove crash (fast fake)")

    bad_durations, bad_failures = collect_samples(broken_run, 4, warmup=0)
    _selftest_assert(bad_durations == [], "broken runner contributes no durations")
    _selftest_assert(len(bad_failures) == 4, "broken runner records every failure")
    unmeasured = build_surface_unmeasured("spot", "no successful prove repetitions; rep[0]: ...")
    _selftest_assert(unmeasured["status"] == "unmeasured", "unmeasured status")
    _selftest_assert("prove" not in unmeasured, "unmeasured surface has NO prove number")

    # 4d. surface_supports_verify predicate (gates the verify fail-closed path).
    _selftest_assert(
        surface_supports_verify("spot", SurfacePlan(generate={"x": 1}, verify={"v": 1})),
        "spot with verify template supports verify",
    )
    _selftest_assert(
        not surface_supports_verify("spot", SurfacePlan(generate={"x": 1})),
        "spot without verify template does NOT support verify",
    )
    _selftest_assert(
        surface_supports_verify("zusd", SurfacePlan(generate={"x": 1}, extra={"verify_builder": "zusd"})),
        "typed surface with verify_builder supports verify",
    )
    _selftest_assert(
        not surface_supports_verify("perps_np", SurfacePlan(generate={"x": 1}, extra={})),
        "typed surface without verify_builder does NOT support verify",
    )

    # 4e. build_verify_request fail-closes (returns None, no KeyError) when a
    #     required ``extra`` is absent — latent crash guard, not a measurement.
    _selftest_assert(
        build_verify_request("zusd", SurfacePlan(generate={}, extra={}), {"meta": {}, "state_hash": "x"}) is None,
        "zusd verify request with missing 'operation' returns None (no KeyError)",
    )
    _selftest_assert(
        build_verify_request("clob", SurfacePlan(generate={}, extra={}), {"meta": {}, "state_hash": "x"}) is None,
        "clob verify request with missing taker/post_book_root returns None",
    )

    # 4f. verify-gate FAIL-CLOSED (the HIGH finding). Drive the REAL decision
    #     function ``finalize_surface`` directly so the test exercises the gate
    #     branch, not a re-implementation. Three cases:
    gate_durations = [1.0, 1.0, 1.0]
    #   (i) supports verify + verify FAILED (ms None) => unmeasured, NO prove.
    gate_fail = finalize_surface(
        "zusd",
        gate_durations,
        requested=3,
        warmup=1,
        supports_verify=True,
        verify_ms=None,
        verify_reason="verify rejected: {'ok': False}",
        failures=[],
    )
    _selftest_assert(gate_fail["status"] == "unmeasured", "verify gate fails surface closed")
    _selftest_assert("prove" not in gate_fail, "failed-verify surface reports NO prove number")
    _selftest_assert("verify failed" in gate_fail["reason"], "verify-gate reason recorded")
    #   (ii) supports verify + verify OK => measured WITH the verify ms.
    gate_ok = finalize_surface(
        "zusd",
        gate_durations,
        requested=3,
        warmup=1,
        supports_verify=True,
        verify_ms=7.5,
        verify_reason="",
        failures=[],
    )
    _selftest_assert(gate_ok["status"] == "measured", "verify ok => measured")
    _selftest_assert(gate_ok["verify_ms_single"] == 7.5, "measured carries verify ms")
    #   (iii) does NOT support verify => verify never gates (measured even with None).
    gate_optional = finalize_surface(
        "noverify",
        gate_durations,
        requested=3,
        warmup=1,
        supports_verify=False,
        verify_ms=None,
        verify_reason="",
        failures=[],
    )
    _selftest_assert(gate_optional["status"] == "measured", "non-verifiable surface stays measured")
    _selftest_assert(gate_optional["verify_ms_single"] is None, "non-verifiable surface verify ms is None")
    #   (iv) no prove durations => unmeasured regardless of verify.
    gate_empty = finalize_surface(
        "zusd",
        [],
        requested=3,
        warmup=1,
        supports_verify=True,
        verify_ms=7.5,
        verify_reason="",
        failures=["rep[0]: prove exit=1"],
    )
    _selftest_assert(gate_empty["status"] == "unmeasured", "no prove reps => unmeasured")
    _selftest_assert("no successful prove" in gate_empty["reason"], "empty-prove reason recorded")

    # 5. simulated BUILD FAILURE => report with all surfaces unmeasured, dev_mode false.
    failed_build_report = build_report(
        environment={"cpu_model": "test", "cpu_count": 1, "risc0_version": "x", "git_commit": "deadbeef"},
        build_cost_s=None,
        build_status="failed",
        build_reason="cargo not found (toolchain absent)",
        surfaces=[build_surface_unmeasured(s, "build unavailable") for s in SURFACES],
        reps=5,
        warmup=0,
    )
    _selftest_assert(failed_build_report["dev_mode"] is False, "dev_mode recorded false")
    _selftest_assert(failed_build_report["build"]["status"] == "failed", "build status failed")
    _selftest_assert(failed_build_report["build"]["cost_s"] is None, "no fabricated build cost")
    _selftest_assert(failed_build_report["measured_count"] == 0, "nothing measured on build failure")
    _selftest_assert(failed_build_report["all_measured"] is False, "all_measured false")
    _selftest_assert(failed_build_report["exec_overhead_s"] is None, "no exec overhead on build failure")

    # 6. JSON + markdown shape on a MEASURED report (mocked durations, no STARK).
    measured = build_surface_measured(
        "perps_np",
        [1.10, 1.05, 1.20, 1.08, 1.15],
        requested=5,
        warmup=1,
        verify_ms=42.5,
        failures=[],
    )
    _selftest_assert(measured["verify_ms_single"] == 42.5, "verify_ms_single field present")
    _selftest_assert("verify_ms" not in measured, "legacy verify_ms key removed")
    report = build_report(
        environment={
            "cpu_model": "Test CPU",
            "cpu_count": 8,
            "risc0_version": "2.3.2",
            "git_commit": "0b2c20c9",
            "prover_backend": "local/default",
            "rayon_num_threads": "unset",
            "load_average": [0.5, 0.4, 0.3],
        },
        build_cost_s=63.2,
        build_status="ok",
        build_reason="",
        surfaces=[measured, build_surface_unmeasured("clob", "clob fixture unreadable")],
        reps=5,
        warmup=1,
        exec_overhead_s=0.018,
    )
    serialized = json.dumps(report)  # must be JSON-serializable
    round_trip = json.loads(serialized)
    _selftest_assert(round_trip["schema"] == SCHEMA, "schema present")
    _selftest_assert(round_trip["build"]["counted_as_prove_time"] is False, "build excluded from prove time")
    _selftest_assert(round_trip["measured_count"] == 1, "one measured surface")
    _selftest_assert(round_trip["exec_overhead_s"] == 0.018, "exec_overhead_s recorded in report")
    md = render_markdown(report)
    _selftest_assert(md.startswith("# RISC0 prove-time benchmark"), "markdown header")
    _selftest_assert("| perps_np | measured |" in md, "measured row in markdown")
    _selftest_assert("| clob | unmeasured |" in md, "unmeasured row in markdown")
    _selftest_assert("42.5" in md, "verify ms in markdown")
    _selftest_assert("exec_overhead_s: 0.018" in md, "exec overhead floor in markdown")
    _selftest_assert("verify_ms_single |" in md, "verify column header renamed")
    # Review fix: unmeasured reason is a footnote, NOT inside the verify column.
    _selftest_assert("Unmeasured surfaces:" in md, "unmeasured reasons rendered as footnotes")
    _selftest_assert("clob fixture unreadable" in md, "unmeasured reason text present (footnote)")
    _selftest_assert("| clob | unmeasured | - | - | - | - | - | - | - |" in md, "unmeasured row all-dashes")
    # p99 footnote marker present for the small-N measured surface.
    _selftest_assert("not a tail estimate" in md, "p99==max caveat rendered")

    # 7. dev-mode REFUSAL is a returned decision (not an exit) in the self-test path.
    _selftest_assert(dev_mode_is_truthy("1") is True, "refuse decision when dev mode on")

    log("self-test: ALL CHECKS PASSED")
    return 0


# --------------------------------------------------------------------------- #
# CLI                                                                          #
# --------------------------------------------------------------------------- #


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Steady-state RISC0 prove-time benchmark (build once, time proves only)."
    )
    parser.add_argument("--repo", type=Path, default=REPO_DEFAULT)
    parser.add_argument("--target-dir", type=Path, default=Path("/tmp/zenodex_bench_prove_target"))
    parser.add_argument("--out", type=Path, default=None, help="writable results JSON path")
    parser.add_argument("--reps", type=int, default=5, help="timed prove repetitions per surface (timed AFTER warmup)")
    parser.add_argument(
        "--warmup",
        type=int,
        default=1,
        help="discarded warm-up proves per surface (default 1 drops the cold first run; 0 to keep it)",
    )
    parser.add_argument("--prove-timeout", type=int, default=600, help="per-prove timeout (s)")
    parser.add_argument("--verify-timeout", type=int, default=120, help="per-verify timeout (s)")
    parser.add_argument("--build-timeout", type=int, default=1200, help="one-time build timeout (s)")
    parser.add_argument("--surface", choices=(*SURFACES, "all"), default="all")
    parser.add_argument("--markdown", action="store_true", help="also render a markdown table to stderr/out")
    parser.add_argument("--self-test", action="store_true", help="validate harness logic (<5s, no STARK); exits 0")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv if argv is not None else sys.argv[1:])

    if args.self_test:
        return run_self_test()

    # DEV-MODE GUARD (load-bearing): refuse to run if RISC0_DEV_MODE is truthy.
    if dev_mode_is_truthy(os.environ.get("RISC0_DEV_MODE")):
        log(
            "REFUSING: RISC0_DEV_MODE is truthy. Dev mode emits FAKE receipts "
            "(~0s) that still 'verify', producing meaningless timing numbers. "
            "Unset RISC0_DEV_MODE (or set it to 0) and re-run."
        )
        return 2

    if args.reps < 1:
        log("--reps must be >= 1")
        return 2

    report = run_benchmark(args)
    emit(report, args)
    # Exit non-zero only on total build failure; per-surface unmeasured still
    # emits the report and is not treated as a harness error.
    if report["build"]["status"] != "ok":
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
