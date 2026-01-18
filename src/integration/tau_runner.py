"""
Tau spec runner utilities (imperative shell).

This module is IO by design: it spawns the `tau` binary and parses outputs.
Keep it out of the functional core.
"""

from __future__ import annotations

import re
import shutil
import os
import select
import signal
import subprocess
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple


ROOT = Path(__file__).resolve().parents[2]


class TauRunError(RuntimeError):
    def __init__(
        self,
        message: str,
        *,
        rc: int,
        stdout: str,
        stderr: str,
        repl_script: str,
        mode: str = "repl",
        spec_text: str = "",
        input_text: str = "",
    ) -> None:
        super().__init__(message)
        self.rc = int(rc)
        self.stdout = str(stdout)
        self.stderr = str(stderr)
        self.repl_script = str(repl_script)
        self.mode = str(mode)
        self.spec_text = str(spec_text)
        self.input_text = str(input_text)


def _run_subprocess_with_output_caps(
    cmd: Sequence[str],
    *,
    input_text: str,
    cwd: Path,
    timeout_s: float,
    max_stdout_bytes: int,
    max_stderr_bytes: int,
) -> Tuple[int, str, str]:
    if not cmd:
        raise ValueError("cmd must be non-empty")
    if not isinstance(timeout_s, (int, float)) or timeout_s <= 0:
        raise ValueError("timeout_s must be positive")
    if not isinstance(max_stdout_bytes, int) or max_stdout_bytes <= 0:
        raise ValueError("max_stdout_bytes must be positive")
    if not isinstance(max_stderr_bytes, int) or max_stderr_bytes <= 0:
        raise ValueError("max_stderr_bytes must be positive")

    try:
        input_bytes = input_text.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise ValueError("input_text must be valid UTF-8") from exc

    proc = subprocess.Popen(
        list(cmd),
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        start_new_session=True,
        close_fds=True,
        cwd=str(cwd),
        bufsize=0,
    )

    assert proc.stdin is not None and proc.stdout is not None and proc.stderr is not None
    stdout_buf = bytearray()
    stderr_buf = bytearray()

    def _decode_stdout() -> str:
        return bytes(stdout_buf).decode("utf-8", errors="replace")

    def _decode_stderr() -> str:
        return bytes(stderr_buf).decode("utf-8", errors="replace")

    def _kill_proc_group() -> None:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            return
        except Exception:
            try:
                proc.kill()
            except Exception:
                return

    try:
        for stream in (proc.stdin, proc.stdout, proc.stderr):
            try:
                os.set_blocking(stream.fileno(), False)
            except Exception:
                _kill_proc_group()
                return -1, _decode_stdout(), "tau requires non-blocking pipes"

        stdin_view = memoryview(input_bytes)
        stdin_off = 0
        stdin_open = True
        stdout_open = True
        stderr_open = True
        if len(stdin_view) == 0:
            stdin_open = False
            try:
                proc.stdin.close()
            except Exception:
                _kill_proc_group()
                return -1, _decode_stdout(), "tau stdin close error"

        deadline = time.monotonic() + float(timeout_s)
        while True:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                _kill_proc_group()
                return -1, _decode_stdout(), "tau timed out"

            rlist = []
            if stdout_open:
                rlist.append(proc.stdout)
            if stderr_open:
                rlist.append(proc.stderr)
            wlist = []
            if stdin_open and stdin_off < len(stdin_view):
                wlist.append(proc.stdin)

            if not rlist and not wlist:
                break

            try:
                ready_r, ready_w, _ = select.select(rlist, wlist, [], min(0.1, remaining))
            except InterruptedError:
                continue
            except Exception as exc:
                _kill_proc_group()
                detail = str(exc).strip()
                if detail:
                    detail = detail[:200]
                    return -1, _decode_stdout(), f"tau select error: {type(exc).__name__}: {detail}"
                return -1, _decode_stdout(), f"tau select error: {type(exc).__name__}"

            for stream in ready_w:
                try:
                    n = stream.write(stdin_view[stdin_off : stdin_off + 4096])
                except BrokenPipeError:
                    stdin_open = False
                    try:
                        stream.close()
                    except Exception:
                        pass
                    continue
                except BlockingIOError:
                    continue
                except Exception:
                    _kill_proc_group()
                    return -1, _decode_stdout(), "tau stdin error"
                if n is None:
                    n = 0
                stdin_off += int(n)
                if stdin_off >= len(stdin_view):
                    stdin_open = False
                    try:
                        proc.stdin.close()
                    except Exception:
                        _kill_proc_group()
                        return -1, _decode_stdout(), "tau stdin close error"

            for stream in ready_r:
                try:
                    chunk = stream.read(4096)
                except BlockingIOError:
                    continue
                except Exception:
                    _kill_proc_group()
                    return -1, _decode_stdout(), "tau stdout/stderr read error"
                if not chunk:
                    if stream is proc.stdout:
                        stdout_open = False
                    elif stream is proc.stderr:
                        stderr_open = False
                    continue

                chunk_b = chunk if isinstance(chunk, (bytes, bytearray)) else str(chunk).encode("utf-8", errors="replace")
                if stream is proc.stdout:
                    stdout_buf += chunk_b
                    if len(stdout_buf) > max_stdout_bytes:
                        stdout_buf[:] = stdout_buf[:max_stdout_bytes]
                        _kill_proc_group()
                        return -1, _decode_stdout(), "tau stdout too large"
                else:
                    stderr_buf += chunk_b
                    if len(stderr_buf) > max_stderr_bytes:
                        stderr_buf[:] = stderr_buf[:max_stderr_bytes]
                        _kill_proc_group()
                        return -1, _decode_stdout(), "tau stderr too large"

            if not stdout_open and not stderr_open and not stdin_open:
                break

        rc = proc.poll()
        if rc is None:
            try:
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    _kill_proc_group()
                    return -1, _decode_stdout(), "tau timed out"
                rc = proc.wait(timeout=remaining)
            except subprocess.TimeoutExpired:
                _kill_proc_group()
                return -1, _decode_stdout(), "tau timed out"
            except Exception:
                _kill_proc_group()
                return -1, _decode_stdout(), "tau did not exit"

        out_s = _decode_stdout()
        err_s = _decode_stderr()
        if stdin_off < len(stdin_view) and int(rc) == 0:
            return -1, out_s, err_s or "tau stdin incomplete write"

        return int(rc), out_s, err_s
    finally:
        try:
            if proc.returncode is None:
                try:
                    _kill_proc_group()
                except Exception:
                    pass
        except Exception:
            pass
        try:
            proc.wait(timeout=1.0)
        except Exception:
            pass


def find_tau_bin(project_root: Path = ROOT) -> Optional[str]:
    """Find a usable Tau binary in common locations or on PATH."""
    candidates = [
        project_root / "external" / "tau-lang" / "build-Release" / "tau",
        project_root / "external" / "tau-lang" / "build-Debug" / "tau",
        project_root / "external" / "tau-nightly" / "usr" / "bin" / "tau",
    ]
    for c in candidates:
        if c.exists() and c.is_file():
            return str(c)
    return shutil.which("tau")


def normalize_spec_text(spec_text: str) -> str:
    """
    Normalize Tau specs for embedding in a REPL harness.

    - Strips comments/blank lines
    - Drops `set charvar ...` lines (we control via CLI flags)
    - Collapses multi-line `always` blocks into single-line `always ... .`
    """
    def _strip_inline_comment(line: str) -> str:
        # Tau uses `#` in bv literals (e.g. `{ #x0000 }`), so treat `#` as a comment
        # marker only when we're not inside `{...}`.
        brace_depth = 0
        for idx, ch in enumerate(line):
            if ch == "{":
                brace_depth += 1
            elif ch == "}":
                brace_depth = max(0, brace_depth - 1)
            elif ch == "#" and brace_depth == 0:
                return line[:idx]
        return line

    lines: list[str] = []
    raw = spec_text.splitlines()
    i = 0
    while i < len(raw):
        line = _strip_inline_comment(raw[i])
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            i += 1
            continue
        if stripped.startswith("set charvar"):
            i += 1
            continue
        if re.match(r"^always\b", stripped):
            expr_parts: list[str] = []
            tail = stripped[len("always") :].strip()
            if tail:
                # Single-line always: `always <expr>.`
                if tail.endswith("."):
                    joined = tail[:-1].strip()
                    if not joined:
                        raise ValueError("empty always expression")
                    lines.append(f"always {joined}.")
                    i += 1
                    continue
                expr_parts.append(tail)
            i += 1
            terminated = False
            while i < len(raw):
                nxt = _strip_inline_comment(raw[i]).strip()
                if not nxt or nxt.startswith("#"):
                    i += 1
                    continue
                expr_parts.append(nxt)
                if nxt.endswith("."):
                    terminated = True
                    break
                i += 1
            if not terminated:
                raise ValueError("unterminated always block (missing '.')")
            joined = " ".join(expr_parts)
            if joined.endswith("."):
                joined = joined[:-1]
            joined = joined.strip()
            if not joined:
                raise ValueError("empty always expression")
            lines.append(f"always {joined}.")
            i += 1
            continue
        lines.append(stripped)
        i += 1
    return "\n".join(lines) + "\n"


@dataclass(frozen=True)
class TauDefinition:
    name: str
    params: tuple[str, ...]
    body: str


_IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
_STREAM_DECL_RE = re.compile(r"^\s*[io]\d+\s*\[[^\]]+\]\s*:")


def parse_definitions(spec_text: str) -> dict[str, TauDefinition]:
    """
    Parse Tau definitions from normalized spec text.

    We only handle the simple, line-based form used throughout this repo:

        name(a : bv[16], b : bv[16]) := <expr>.

    The returned bodies are un-terminated (no trailing '.').
    """
    defs: dict[str, TauDefinition] = {}
    for line in spec_text.splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        if re.match(r"^always\b", stripped):
            continue
        # Skip stream declaration hints like `i1[t]:bv[16]`.
        if _STREAM_DECL_RE.match(line):
            continue
        if re.match(r"^\s*[io]\d+\s*:", line):
            continue

        match = re.match(r"^([A-Za-z_][A-Za-z0-9_]*)\((.*)\)\s*:=\s*(.*)\.\s*$", stripped)
        if not match:
            continue
        name, params_raw, body = match.group(1), match.group(2), match.group(3)
        params: list[str] = []
        for p in [p.strip() for p in params_raw.split(",") if p.strip()]:
            # Allow `x : bv[16]` and tolerate stray type-like tokens.
            p_name = p.split(":", 1)[0].strip()
            if " " in p_name:
                p_name = p_name.split()[-1]
            if not p_name or not _IDENT_RE.fullmatch(p_name):
                raise ValueError(f"Invalid parameter name in {name}(..): {p!r}")
            params.append(p_name)
        defs[name] = TauDefinition(name=name, params=tuple(params), body=body.strip())
    return defs


def _split_call_args(arglist: str) -> list[str]:
    args: list[str] = []
    buf: list[str] = []
    paren = 0
    bracket = 0
    brace = 0
    for ch in arglist:
        if ch == "(":
            paren += 1
        elif ch == ")":
            paren -= 1
        elif ch == "[":
            bracket += 1
        elif ch == "]":
            bracket -= 1
        elif ch == "{":
            brace += 1
        elif ch == "}":
            brace -= 1
        elif ch == "," and paren == 0 and bracket == 0 and brace == 0:
            args.append("".join(buf).strip())
            buf.clear()
            continue
        buf.append(ch)
    tail = "".join(buf).strip()
    if tail:
        args.append(tail)
    return args


def _replace_identifier(text: str, ident: str, replacement: str) -> str:
    pattern = re.compile(rf"(?<![A-Za-z0-9_]){re.escape(ident)}(?![A-Za-z0-9_])")
    return pattern.sub(replacement, text)


def inline_definitions(expr: str, defs: dict[str, TauDefinition], *, max_depth: int = 25) -> str:
    """
    Inline (macro-expand) simple Tau definitions into `expr`.

    Tau's current REPL `run` mode is fragile with user-defined functions/predicates.
    We inline definitions as a pragmatic workaround for local testing.
    """
    if not defs:
        return expr
    if max_depth <= 0:
        raise ValueError("Tau inlining exceeded max_depth (recursive definitions?)")

    out: list[str] = []
    i = 0
    while i < len(expr):
        match = _IDENT_RE.match(expr, i)
        if not match:
            out.append(expr[i])
            i += 1
            continue

        name = match.group(0)
        j = match.end()
        if name in defs and j < len(expr) and expr[j] == "(":
            depth = 0
            k = j
            while k < len(expr):
                ch = expr[k]
                if ch == "(":
                    depth += 1
                elif ch == ")":
                    depth -= 1
                    if depth == 0:
                        break
                k += 1
            if depth != 0 or k >= len(expr) or expr[k] != ")":
                raise ValueError(f"Unbalanced parentheses when parsing call: {expr[i:i+80]!r}")

            arglist = expr[j + 1 : k]
            args = _split_call_args(arglist)
            definition = defs[name]
            if len(args) != len(definition.params):
                out.append(expr[i : k + 1])
                i = k + 1
                continue

            expanded_args = [inline_definitions(a.strip(), defs, max_depth=max_depth - 1) for a in args]
            body = definition.body
            for param, arg in zip(definition.params, expanded_args):
                body = _replace_identifier(body, param, f"({arg})")
            body = inline_definitions(body, defs, max_depth=max_depth - 1)
            out.append(f"({body})")
            i = k + 1
            continue

        out.append(name)
        i = j

    return "".join(out)


def extract_stream_types(spec_text: str) -> dict[str, str]:
    """
    Extract stream types like:
    - i1[t]:bv[16]
    - o1[t]:sbf
    """
    stream_types: dict[str, str] = {}
    for match in re.finditer(r"\b([io]\d+)\s*\[[^\]]+\]\s*:\s*([a-zA-Z]+\[\d+\]|[a-zA-Z]+)", spec_text):
        name = match.group(1)
        if name not in stream_types:
            stream_types[name] = match.group(2)
    return stream_types


def extract_always_exprs(spec_text: str) -> list[str]:
    exprs: list[str] = []
    for line in spec_text.splitlines():
        stripped = line.strip()
        if stripped.startswith("#"):
            continue
        if not re.match(r"^always\b", stripped):
            continue
        match = re.search(r"always\s*(.*)\.\s*$", stripped)
        if match:
            exprs.append(match.group(1))
    return exprs


def build_repl_script(
    *,
    spec_text: str,
    input_streams: dict[str, str],
    output_streams: dict[str, str],
    input_paths: dict[str, Path],
    output_paths: dict[str, Path],
    always_exprs: list[str],
    skip_definitions: bool = True,
) -> str:
    lines: list[str] = []
    lines.append("# Auto-generated Tau REPL harness")
    lines.append("")

    # If we are skipping definitions (because we inline them into always-exprs),
    # we must skip the *entire* definition block. Tau definitions commonly span
    # multiple lines until a terminating '.'.
    skipping_def_block = False

    for name in sorted(input_streams.keys(), key=lambda s: int(s[1:])):
        lines.append(f'{name} : {input_streams[name]} = in file("{input_paths[name]}")')

    lines.append("")
    for name in sorted(output_streams.keys(), key=lambda s: int(s[1:])):
        lines.append(f'{name} : {output_streams[name]} = out file("{output_paths[name]}")')

    lines.append("")
    for line in spec_text.splitlines():
        if line.lstrip().startswith("#"):
            continue
        if re.match(r"^run\b", line.strip()):
            continue
        if re.match(r"^always\b", line.strip()):
            continue
        # Optionally drop `:=` definitions (when we inline them into always-exprs).
        # IMPORTANT: definitions may span multiple lines until a '.' terminator.
        if skip_definitions:
            if skipping_def_block:
                if line.strip().endswith("."):
                    skipping_def_block = False
                continue
            if ":=" in line:
                # Begin skipping at the definition header line.
                if not line.strip().endswith("."):
                    skipping_def_block = True
                continue
        # Avoid redeclaring streams: spec files typically include `iN[t]:...` / `oN[t]:...`.
        if _STREAM_DECL_RE.match(line):
            continue
        if re.match(r"^\s*[io]\d+\s*:", line):
            continue
        if line.strip():
            lines.append(line)

    expr = " && ".join(f"({expr})" for expr in always_exprs)
    lines.append("")
    lines.append(f"r {expr}")
    lines.append("q")
    lines.append("")
    return "\n".join(lines)


def run_tau_spec_steps(
    tau_bin: str,
    spec_path: Path,
    steps: List[Dict[str, int]],
    *,
    timeout_s: float = 2.0,
) -> Dict[int, Dict[str, int]]:
    """
    Run a Tau spec over a list of concrete steps (IO harness, REPL mode).

    `steps[k]` should contain keys like `i1`, `i2`, ... as integers.
    Returns `outputs_by_step[step_index]['o1'] = 0|1|...`.
    """
    if not steps:
        return {}
    if len(steps) > 10_000:
        raise ValueError(f"too many Tau steps: {len(steps)} > 10000")
    if not tau_bin:
        raise ValueError("tau_bin must be provided")
    if not spec_path.exists():
        raise FileNotFoundError(f"Tau spec not found: {spec_path}")

    spec_text = normalize_spec_text(spec_path.read_text(encoding="utf-8"))
    stream_types = extract_stream_types(spec_text)
    input_streams = {k: v for k, v in stream_types.items() if k.startswith("i")}
    output_streams = {k: v for k, v in stream_types.items() if k.startswith("o")}
    always_exprs = extract_always_exprs(spec_text)

    defs = parse_definitions(spec_text)
    expanded_always_exprs = [inline_definitions(expr, defs) for expr in always_exprs]

    if not input_streams:
        raise ValueError(f"No input streams detected in spec: {spec_path}")
    if not output_streams:
        raise ValueError(f"No output streams detected in spec: {spec_path}")
    if not always_exprs:
        raise ValueError(f"Missing always constraint in spec: {spec_path}")

    with tempfile.TemporaryDirectory() as tmpdir:
        tmpdir_path = Path(tmpdir)
        input_paths: dict[str, Path] = {}
        output_paths: dict[str, Path] = {}

        for name in sorted(input_streams.keys(), key=lambda s: int(s[1:])):
            values: list[str] = []
            for step in steps:
                if name not in step:
                    raise ValueError(f"Missing {name} in Tau inputs for spec {spec_path}")
                v = step[name]
                if not isinstance(v, int) or isinstance(v, bool):
                    raise ValueError(f"{name} must be an int, got {v!r}")
                values.append(str(v))
            path = tmpdir_path / f"{name}.in"
            path.write_text("\n".join(values) + "\n", encoding="utf-8")
            input_paths[name] = path

        for name in sorted(output_streams.keys(), key=lambda s: int(s[1:])):
            output_paths[name] = tmpdir_path / f"{name}.out"

        repl_script = build_repl_script(
            spec_text=spec_text,
            input_streams=input_streams,
            output_streams=output_streams,
            input_paths=input_paths,
            output_paths=output_paths,
            always_exprs=expanded_always_exprs,
            skip_definitions=True,
        )

        rc, out, err = _run_subprocess_with_output_caps(
            [tau_bin, "--severity", "error", "--charvar", "false"],
            input_text=repl_script,
            cwd=spec_path.parent,
            timeout_s=timeout_s,
            max_stdout_bytes=32_000,
            max_stderr_bytes=8_000,
        )
        if rc != 0:
            detail = (err or out or "unknown error").strip()
            raise RuntimeError(f"tau failed (rc={rc}): {detail[:400]}")

        outputs_by_step: Dict[int, Dict[str, int]] = {}
        for name, path in output_paths.items():
            if not path.exists():
                raise RuntimeError(f"tau did not create output file: {name}")
            max_bytes = (len(steps) * 64) + 1024
            try:
                if path.stat().st_size > max_bytes:
                    raise RuntimeError(f"{name} output file too large: {path.stat().st_size} > {max_bytes} bytes")
            except OSError:
                raise RuntimeError(f"could not stat tau output file: {name}")
            values = [line.strip() for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]
            if len(values) != len(steps):
                raise RuntimeError(
                    f"{name} output length mismatch: expected {len(steps)} line(s), got {len(values)}"
                )
            for idx, raw in enumerate(values):
                try:
                    value = int(raw)
                except ValueError as exc:
                    raise RuntimeError(f"{name} output non-integer value: {raw!r}") from exc
                outputs_by_step.setdefault(idx, {})[name] = value

    return outputs_by_step


def run_tau_spec_steps_with_trace(
    tau_bin: str,
    spec_path: Path,
    steps: List[Dict[str, int]],
    *,
    timeout_s: float = 2.0,
    severity: str = "trace",
    inline_defs: bool = True,
    experimental: bool = False,
) -> Tuple[Dict[int, Dict[str, int]], str, str, str]:
    """
    Like `run_tau_spec_steps`, but returns (outputs_by_step, stdout, stderr, repl_script)
    so callers can archive execution traces for evidence/analysis.
    """
    if severity not in {"trace", "debug", "info", "error"}:
        raise ValueError(f"invalid severity: {severity!r}")
    if not steps:
        return {}, "", "", ""
    if len(steps) > 10_000:
        raise ValueError(f"too many Tau steps: {len(steps)} > 10000")
    if not tau_bin:
        raise ValueError("tau_bin must be provided")
    if not spec_path.exists():
        raise FileNotFoundError(f"Tau spec not found: {spec_path}")

    spec_text = normalize_spec_text(spec_path.read_text(encoding="utf-8"))
    stream_types = extract_stream_types(spec_text)
    input_streams = {k: v for k, v in stream_types.items() if k.startswith("i")}
    output_streams = {k: v for k, v in stream_types.items() if k.startswith("o")}
    always_exprs = extract_always_exprs(spec_text)

    defs = parse_definitions(spec_text)
    expanded_always_exprs = [inline_definitions(expr, defs) for expr in always_exprs] if inline_defs else list(always_exprs)

    if not input_streams:
        raise ValueError(f"No input streams detected in spec: {spec_path}")
    if not output_streams:
        raise ValueError(f"No output streams detected in spec: {spec_path}")
    if not always_exprs:
        raise ValueError(f"Missing always constraint in spec: {spec_path}")

    with tempfile.TemporaryDirectory() as tmpdir:
        tmpdir_path = Path(tmpdir)
        input_paths: dict[str, Path] = {}
        output_paths: dict[str, Path] = {}

        for name in sorted(input_streams.keys(), key=lambda s: int(s[1:])):
            values: list[str] = []
            for step in steps:
                if name not in step:
                    raise ValueError(f"Missing {name} in Tau inputs for spec {spec_path}")
                v = step[name]
                if not isinstance(v, int) or isinstance(v, bool):
                    raise ValueError(f"{name} must be an int, got {v!r}")
                values.append(str(v))
            path = tmpdir_path / f"{name}.in"
            path.write_text("\n".join(values) + "\n", encoding="utf-8")
            input_paths[name] = path

        for name in sorted(output_streams.keys(), key=lambda s: int(s[1:])):
            output_paths[name] = tmpdir_path / f"{name}.out"

        repl_script = build_repl_script(
            spec_text=spec_text,
            input_streams=input_streams,
            output_streams=output_streams,
            input_paths=input_paths,
            output_paths=output_paths,
            always_exprs=expanded_always_exprs,
            skip_definitions=bool(inline_defs),
        )

        cmd = [tau_bin]
        if experimental:
            cmd.append("--experimental")
        cmd += ["--severity", severity, "--charvar", "false"]

        rc, out, err = _run_subprocess_with_output_caps(
            cmd,
            input_text=repl_script,
            cwd=spec_path.parent,
            timeout_s=timeout_s,
            max_stdout_bytes=512_000,
            max_stderr_bytes=128_000,
        )
        if rc != 0:
            detail = (err or out or "unknown error").strip()
            raise TauRunError(
                f"tau failed (rc={rc}): {detail[:400]}",
                rc=rc,
                stdout=out,
                stderr=err,
                repl_script=repl_script,
            )

        outputs_by_step: Dict[int, Dict[str, int]] = {}
        for name, path in output_paths.items():
            if not path.exists():
                raise TauRunError(
                    f"tau did not create output file: {name}",
                    rc=rc,
                    stdout=out,
                    stderr=err,
                    repl_script=repl_script,
                )
            max_bytes = (len(steps) * 64) + 1024
            try:
                if path.stat().st_size > max_bytes:
                    raise TauRunError(
                        f"{name} output file too large: {path.stat().st_size} > {max_bytes} bytes",
                        rc=rc,
                        stdout=out,
                        stderr=err,
                        repl_script=repl_script,
                    )
            except OSError:
                raise TauRunError(
                    f"could not stat tau output file: {name}",
                    rc=rc,
                    stdout=out,
                    stderr=err,
                    repl_script=repl_script,
                )
            values = [line.strip() for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]
            if len(values) != len(steps):
                raise TauRunError(
                    f"{name} output length mismatch: expected {len(steps)} line(s), got {len(values)}",
                    rc=rc,
                    stdout=out,
                    stderr=err,
                    repl_script=repl_script,
                )
            for idx, raw in enumerate(values):
                try:
                    value = int(raw)
                except ValueError as exc:
                    raise TauRunError(
                        f"{name} output non-integer value: {raw!r}",
                        rc=rc,
                        stdout=out,
                        stderr=err,
                        repl_script=repl_script,
                    ) from exc
                outputs_by_step.setdefault(idx, {})[name] = value

        return outputs_by_step, out, err, repl_script


def run_tau_spec_steps_spec_mode(
    tau_bin: str,
    spec_path: Path,
    steps: List[Dict[str, int]],
    *,
    timeout_s: float = 2.0,
    severity: str = "error",
    experimental: bool = False,
) -> Dict[int, Dict[str, int]]:
    """
    Run a Tau spec by invoking Tau in "spec mode" (`tau <file> -x`) and parse stdout.

    This is useful for trace analysis when specs are known to be compatible with
    Tau's file-runner. We normalize the spec text into a temp file to avoid
    REPL-only directives (e.g. `set charvar ...`) and to collapse multi-line
    `always` blocks into the single-line form that Tau's file-runner is stricter about.
    """
    outputs, _, _, _, _ = run_tau_spec_steps_spec_mode_with_trace(
        tau_bin=tau_bin,
        spec_path=spec_path,
        steps=steps,
        timeout_s=timeout_s,
        severity=severity,
        experimental=experimental,
    )
    return outputs


def run_tau_spec_steps_spec_mode_with_trace(
    tau_bin: str,
    spec_path: Path,
    steps: List[Dict[str, int]],
    *,
    timeout_s: float = 2.0,
    severity: str = "error",
    experimental: bool = False,
) -> Tuple[Dict[int, Dict[str, int]], str, str, str, str]:
    """
    Spec-mode runner with trace capture.

    Returns:
      (outputs_by_step, stdout, stderr, normalized_spec_text, input_text)
    """
    if not steps:
        return {}, "", "", "", ""
    if len(steps) > 10_000:
        raise ValueError(f"too many Tau steps: {len(steps)} > 10000")
    if not tau_bin:
        raise ValueError("tau_bin must be provided")
    if not spec_path.exists():
        raise FileNotFoundError(f"Tau spec not found: {spec_path}")

    raw_spec_text = spec_path.read_text(encoding="utf-8")
    spec_text = normalize_spec_text(raw_spec_text)
    stream_types = extract_stream_types(spec_text)
    input_streams = {k: v for k, v in stream_types.items() if k.startswith("i")}
    if not input_streams:
        raise ValueError(f"No input streams detected in spec: {spec_path}")

    # Tau's file-runner prompts in lexicographic order (i1, i10, i11, ..., i2, ...),
    # so we must feed inputs in that same order.
    input_names = sorted(input_streams.keys())
    lines: list[str] = []
    for step in steps:
        for name in input_names:
            if name not in step:
                raise ValueError(f"Missing {name} in Tau inputs for spec {spec_path}")
            v = step[name]
            if not isinstance(v, int) or isinstance(v, bool):
                raise ValueError(f"{name} must be an int, got {v!r}")
            lines.append(str(v))

    if severity not in {"trace", "debug", "info", "error"}:
        raise ValueError(f"invalid severity: {severity!r}")

    # Tau's `-x` runner is interactive: after consuming the requested values for the
    # last step, it will prompt again. Sending a final blank line terminates cleanly.
    input_text = "\n".join(lines) + "\n\n"

    with tempfile.TemporaryDirectory() as tmpdir:
        tmpdir_path = Path(tmpdir)
        tmp_spec_path = tmpdir_path / spec_path.name
        tmp_spec_path.write_text(spec_text, encoding="utf-8")

        cmd = [tau_bin, str(tmp_spec_path)]
        if experimental:
            cmd.append("--experimental")
        cmd += ["--severity", severity, "--charvar", "false", "-x"]

        rc, out, err = _run_subprocess_with_output_caps(
            cmd,
            input_text=input_text,
            cwd=tmpdir_path,
            timeout_s=timeout_s,
            max_stdout_bytes=256_000,
            max_stderr_bytes=32_000,
        )

    if rc != 0:
        detail = (err or out or "unknown error").strip()
        raise TauRunError(
            f"tau failed (rc={rc}): {detail[:400]}",
            rc=rc,
            stdout=out,
            stderr=err,
            repl_script="",
            mode="spec",
            spec_text=spec_text,
            input_text=input_text,
        )

    output_text = out + ("\n" + err if err else "")
    outputs_by_step: Dict[int, Dict[str, int]] = {}
    for line in output_text.splitlines():
        for match in re.finditer(r"\b(o\d+)\[(\d+)\]:[^\s:=]+\s*:=\s*(-?\d+)", line):
            name = match.group(1)
            idx = int(match.group(2))
            value = int(match.group(3))
            outputs_by_step.setdefault(idx, {})[name] = value

    return outputs_by_step, out, err, spec_text, input_text


def split_u32(x: int) -> tuple[int, int]:
    """Split an unsigned 32-bit integer into (hi16, lo16)."""
    if not isinstance(x, int) or isinstance(x, bool) or x < 0 or x > 0xFFFFFFFF:
        raise ValueError(f"Value out of u32 range: {x}")
    return (x >> 16) & 0xFFFF, x & 0xFFFF
