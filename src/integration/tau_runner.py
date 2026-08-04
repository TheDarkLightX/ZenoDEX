"""
Tau spec runner utilities (imperative shell).

This module is IO by design: it spawns the `tau` binary (or, optionally,
uses Tau's Python bindings) and parses outputs.
Keep it out of the functional core.
"""

from __future__ import annotations

import importlib
import os
import re
import select
import shutil
import signal
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path
from types import ModuleType
from typing import Any, Dict, List, Optional, Sequence, Tuple

ROOT = Path(__file__).resolve().parents[2]

_ANSI_ESCAPE_RE = re.compile(
    r"\x1b(?:\[[0-?]*[ -/]*[@-~]|\][^\x07]*(?:\x07|\x1b\\))"
)


def strip_ansi(text: str) -> str:
    """Remove terminal control sequences before inspecting Tau diagnostics."""
    return _ANSI_ESCAPE_RE.sub("", str(text))


def has_tau_error_diagnostic(*texts: str) -> bool:
    """Return whether any Tau output contains its canonical ``(Error)`` marker."""
    return any("(Error)" in strip_ansi(text) for text in texts if text)


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

    if proc.stdin is None or proc.stdout is None or proc.stderr is None:
        try:
            proc.kill()
        except Exception:
            pass
        raise RuntimeError("tau subprocess misconfigured: stdin/stdout/stderr pipes unavailable")
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


def find_tau_bin(project_root: Path = ROOT, *, profile: str | None = None) -> Optional[str]:
    """Find a usable Tau binary in common locations or on PATH."""

    def is_executable(path: Path) -> bool:
        try:
            return path.exists() and path.is_file() and os.access(str(path), os.X_OK)
        except Exception:
            return False

    env_tau = os.environ.get("TAU_BIN", "").strip()
    if env_tau:
        p = Path(os.path.expanduser(env_tau))
        if is_executable(p):
            return str(p)

    selected_profile = (profile or os.environ.get("TAU_BIN_PROFILE", "runtime")).strip().lower()
    if selected_profile in {"", "default"}:
        selected_profile = "runtime"

    env_profile_var = {
        "runtime": "TAU_RUNTIME_BIN",
        "stable": "TAU_RUNTIME_BIN",
        "testnet": "TAU_RUNTIME_BIN",
        "latest": "TAU_LATEST_BIN",
        "current": "TAU_LATEST_BIN",
        "research": "TAU_LATEST_BIN",
    }.get(selected_profile)
    if env_profile_var:
        env_profile_tau = os.environ.get(env_profile_var, "").strip()
        if env_profile_tau:
            p = Path(os.path.expanduser(env_profile_tau))
            if is_executable(p):
                return str(p)

    stable_candidates = [
        project_root / "external" / "tau-lang-bitblasting-prev-eea8fb1f" / "build-Release" / "tau",
        project_root / "external" / "tau-lang-bitblasting-prev-eea8fb1f" / "build-Release-fresh" / "tau",
    ]
    latest_candidates = [
        project_root / "external" / "tau-lang" / "build-Release" / "tau",
        project_root / "external" / "tau-lang" / "build-Debug" / "tau",
        project_root / "external" / "tau-lang-upstream-main" / "build-Release" / "tau",
    ]
    if selected_profile in {"latest", "current", "research"}:
        candidates = latest_candidates + stable_candidates + [
            project_root / "external" / "tau-nightly" / "usr" / "bin" / "tau",
        ]
    else:
        candidates = stable_candidates + latest_candidates + [
            project_root / "external" / "tau-nightly" / "usr" / "bin" / "tau",
        ]
    for c in candidates:
        if is_executable(c):
            return str(c)
    return shutil.which("tau")


def _find_tau_python_binding_dirs(project_root: Path = ROOT) -> list[Path]:
    """
    Return candidate directories that may contain the compiled Tau Python extension.

    Tau's nanobind build produces an extension named `tau.*.so` (or `.pyd`).
    We keep this purely best-effort and do not raise on missing paths.
    """
    build_roots = [
        project_root / "external" / "tau-lang" / "build-Release",
        project_root / "external" / "tau-lang" / "build-Debug",
    ]
    exts = (".so", ".pyd", ".dylib")
    dirs: set[Path] = set()
    for root in build_roots:
        if not root.exists():
            continue
        for ext in exts:
            for p in root.rglob(f"tau*{ext}"):
                if p.is_file():
                    dirs.add(p.parent)
    return sorted(dirs)


def _try_import_tau_python_binding(project_root: Path = ROOT) -> Optional[ModuleType]:
    """
    Attempt to import Tau's Python bindings (built via `-DTAU_BUILD_BINDING_PYTHON=ON`).

    Returns the imported module on success, else None.

    IMPORTANT: This is best-effort tooling only. For consensus-critical verification,
    prefer running the standalone `tau` binary in a separate process.
    """
    candidates = _find_tau_python_binding_dirs(project_root)
    if not candidates:
        return None

    old_sys_path = list(sys.path)
    try:
        # Prepend all candidate directories. Once the extension is imported, it
        # lives in `sys.modules` and doesn't require `sys.path` persistence.
        for d in reversed(candidates):
            ds = str(d)
            if ds not in sys.path:
                sys.path.insert(0, ds)
        try:
            mod = importlib.import_module("tau")
        except Exception:
            return None

        # Guard against importing an unrelated `tau` package.
        if not hasattr(mod, "get_interpreter") or not hasattr(mod, "get_inputs_for_step") or not hasattr(mod, "step"):
            return None

        return mod
    finally:
        sys.path = old_sys_path


def _run_tau_spec_steps_via_python_binding(
    spec_path: Path,
    steps: List[Dict[str, int]],
    *,
    timeout_s: float,
    project_root: Path = ROOT,
) -> Dict[int, Dict[str, int]]:
    tau = _try_import_tau_python_binding(project_root=project_root)
    if tau is None:
        raise RuntimeError(
            "Tau Python bindings not available. Build Tau with "
            "`-DTAU_BUILD_BINDING_PYTHON=ON` and ensure the resulting `tau.*.so` "
            "is discoverable (this repo's helper searches under external/tau-lang/build-*)."
        )

    if not spec_path.exists():
        raise FileNotFoundError(f"Tau spec not found: {spec_path}")

    raw_spec_text = spec_path.read_text(encoding="utf-8")
    spec_text = normalize_spec_text(raw_spec_text)
    stream_types = extract_stream_types(spec_text)
    input_streams = {k: v for k, v in stream_types.items() if k.startswith("i")}
    output_streams = {k: v for k, v in stream_types.items() if k.startswith("o")}
    always_exprs = extract_always_exprs(spec_text)
    defs = parse_definitions(spec_text)

    if not always_exprs:
        raise RuntimeError(
            "Tau Python-binding runner currently supports only specs that use "
            "`always ... .` clauses (so it can compile them into a single expression for the API)."
        )

    # NOTE: Tau's string API expects a spec expression like:
    #   (<expr1>) && (<expr2>) .
    # not our REPL-friendly multi-line `always ... .` directives.
    expanded_always_exprs = [inline_definitions(expr, defs) for expr in always_exprs]
    spec_expr = " && ".join(f"({expr})" for expr in expanded_always_exprs if expr.strip())
    if not spec_expr:
        raise RuntimeError("empty always expression after normalization/inlining")
    spec_for_api = spec_expr + "."

    # Defensive posture: we observed reproducible segfaults in Tau's Python bindings
    # when stepping specs that have sbf-typed *inputs* (e.g. i1[t]:sbf). Fail closed
    # and require the subprocess runner for those specs.
    for in_name, in_type in input_streams.items():
        if in_type == "sbf":
            raise RuntimeError(
                f"Tau Python bindings unsafe for sbf input stream {in_name} "
                f"(spec: {spec_path.name}); use the tau subprocess runner instead."
            )

    opts = tau.interpreter_options()
    in_stream_objs: dict[str, object] = {}
    # The nanobind module is loaded dynamically, so no static stream class is
    # available here. Keep Any confined to this external-binding boundary.
    out_stream_objs: dict[str, Any] = {}

    for name in sorted(input_streams.keys(), key=lambda s: int(s[1:])):
        values: list[str] = []
        for step in steps:
            if name not in step:
                raise ValueError(f"Missing {name} in Tau inputs for spec {spec_path}")
            v = step[name]
            if not isinstance(v, int) or isinstance(v, bool):
                raise ValueError(f"{name} must be an int, got {v!r}")
            values.append(str(v))
        stream = tau.vector_input_stream(values)
        opts.input_remaps[name] = stream
        in_stream_objs[name] = stream

    for name in sorted(output_streams.keys(), key=lambda s: int(s[1:])):
        stream = tau.vector_output_stream()
        opts.output_remaps[name] = stream
        out_stream_objs[name] = stream

    interp = tau.get_interpreter(spec_for_api, opts)
    if interp is None:
        raise RuntimeError(f"tau.get_interpreter returned None for spec: {spec_path}")

    started = time.monotonic()
    for _ in range(len(steps)):
        if (time.monotonic() - started) > float(timeout_s):
            raise RuntimeError(f"tau python binding runner timed out after {timeout_s}s")
        # IMPORTANT: do not use `get_inputs_for_step` + `step(i, inputs)` here.
        # We observed segfaults in the current nanobind layer for map-typed inputs.
        tau.step(interp)

    outputs_by_step: Dict[int, Dict[str, int]] = {}
    for out_name, out_stream in out_stream_objs.items():
        values = out_stream.get_values()
        if len(values) != len(steps):
            raise RuntimeError(
                f"{out_name} output length mismatch: expected {len(steps)} line(s), got {len(values)}"
            )
        for idx, raw in enumerate(values):
            raw_s = str(raw).strip()
            try:
                value = int(raw_s)
            except Exception as exc:
                raise RuntimeError(f"{out_name} output non-integer value: {raw_s!r}") from exc
            outputs_by_step.setdefault(idx, {})[out_name] = value

    return outputs_by_step


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
_OUTPUT_ASSIGN_RE = re.compile(r"\b(o\d+)\[(\d+)\](?::[^\s:=]+)?\s*:=\s*(-?\d+)")


def parse_definitions(spec_text: str) -> dict[str, TauDefinition]:
    """
    Parse Tau definitions from normalized spec text.

    Supports both single-line and multiline definitions:

        name(a : bv[16], b : bv[16]) := <expr>.
        name(a : bv[16], b : bv[16]) :=
          <expr_part_1> &&
          <expr_part_2>.

    The returned bodies are un-terminated (no trailing '.').
    """
    defs: dict[str, TauDefinition] = {}
    lines = spec_text.splitlines()
    i = 0
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            i += 1
            continue
        if re.match(r"^always\b", stripped):
            i += 1
            continue
        # Skip stream declaration hints like `i1[t]:bv[16]`.
        if _STREAM_DECL_RE.match(line):
            i += 1
            continue
        if re.match(r"^\s*[io]\d+\s*:", line):
            i += 1
            continue

        match = re.match(r"^([A-Za-z_][A-Za-z0-9_]*)\((.*)\)\s*:=\s*(.*)$", stripped)
        if not match:
            i += 1
            continue

        name, params_raw = match.group(1), match.group(2)
        body_parts: list[str] = []
        first_body = match.group(3).strip()
        if first_body:
            body_parts.append(first_body)

        while True:
            if body_parts and body_parts[-1].endswith("."):
                break
            i += 1
            if i >= len(lines):
                raise ValueError(f"unterminated definition body for {name}(..)")
            nxt = lines[i].strip()
            if not nxt or nxt.startswith("#"):
                continue
            body_parts.append(nxt)

        body_joined = " ".join(body_parts).strip()
        if not body_joined.endswith("."):
            raise ValueError(f"unterminated definition body for {name}(..)")
        body = body_joined[:-1].strip()

        params: list[str] = []
        for p in [p.strip() for p in params_raw.split(",") if p.strip()]:
            # Allow `x : bv[16]` and tolerate stray type-like tokens.
            p_name = p.split(":", 1)[0].strip()
            if " " in p_name:
                p_name = p_name.split()[-1]
            if not p_name or not _IDENT_RE.fullmatch(p_name):
                raise ValueError(f"Invalid parameter name in {name}(..): {p!r}")
            params.append(p_name)

        defs[name] = TauDefinition(name=name, params=tuple(params), body=body)
        i += 1
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
            for param, arg in zip(definition.params, expanded_args, strict=True):
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


def _extract_outputs_from_text(output_text: str) -> Dict[int, Dict[str, int]]:
    outputs_by_step: Dict[int, Dict[str, int]] = {}
    for match in _OUTPUT_ASSIGN_RE.finditer(output_text):
        name = match.group(1)
        idx = int(match.group(2))
        value = int(match.group(3))
        if name in outputs_by_step.get(idx, {}):
            raise ValueError(f"duplicate Tau output assignment: {name}[{idx}]")
        outputs_by_step.setdefault(idx, {})[name] = value
    return outputs_by_step


def _outputs_complete(
    *,
    outputs_by_step: Dict[int, Dict[str, int]],
    out_names: Sequence[str],
    step_count: int,
) -> bool:
    for idx in range(step_count):
        got = outputs_by_step.get(idx, {})
        for out_name in out_names:
            if out_name not in got:
                return False
    return True


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
        in_path = str(input_paths[name]).replace("\\", "\\\\").replace('"', '\\"')
        lines.append(f'{name} : {input_streams[name]} := in file("{in_path}")')

    lines.append("")
    for name in sorted(output_streams.keys(), key=lambda s: int(s[1:])):
        out_path = str(output_paths[name]).replace("\\", "\\\\").replace('"', '\\"')
        lines.append(f'{name} : {output_streams[name]} := out file("{out_path}")')

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
    tau_bin: Optional[str],
    spec_path: Path,
    steps: List[Dict[str, int]],
    *,
    timeout_s: float = 2.0,
    experimental: bool = False,
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
    if not spec_path.exists():
        raise FileNotFoundError(f"Tau spec not found: {spec_path}")
    if not tau_bin:
        if os.environ.get("TAU_USE_PY_BINDINGS") != "1":
            raise ValueError(
                "tau_bin must be provided (or set TAU_USE_PY_BINDINGS=1 to enable Tau Python bindings fallback)"
            )
        return _run_tau_spec_steps_via_python_binding(spec_path, steps, timeout_s=timeout_s)

    tau_bin_path = Path(str(tau_bin)).expanduser()
    if not tau_bin_path.is_absolute():
        # Many runners execute Tau with `cwd=spec_path.parent`, so relative `tau_bin`
        # paths are fragile. Resolve relative to the repo root.
        tau_bin_path = (ROOT / tau_bin_path).resolve()
    else:
        tau_bin_path = tau_bin_path.resolve()
    if not tau_bin_path.exists() or not tau_bin_path.is_file():
        raise FileNotFoundError(f"Tau binary not found: {tau_bin_path}")
    if not os.access(str(tau_bin_path), os.X_OK):
        raise PermissionError(f"Tau binary not executable: {tau_bin_path}")
    tau_bin = str(tau_bin_path)

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

        cmd = [tau_bin]
        if experimental:
            cmd.append("--experimental")
        cmd += ["--severity", "error", "--charvar", "false"]

        rc, out, err = _run_subprocess_with_output_caps(
            cmd,
            input_text=repl_script,
            cwd=spec_path.parent,
            timeout_s=timeout_s,
            max_stdout_bytes=32_000,
            max_stderr_bytes=8_000,
        )
        if rc != 0:
            detail = (err or out or "unknown error").strip()
            raise RuntimeError(f"tau failed (rc={rc}): {detail[:400]}")
        if has_tau_error_diagnostic(out, err):
            detail = (err or out or "Tau reported an error diagnostic").strip()
            raise RuntimeError(f"tau reported an error diagnostic (rc=0): {detail[:400]}")

        outputs_by_step: Dict[int, Dict[str, int]] = {}
        missing_outputs: list[str] = []
        for name, path in output_paths.items():
            if not path.exists():
                missing_outputs.append(name)
                continue
            max_bytes = (len(steps) * 64) + 1024
            try:
                if path.stat().st_size > max_bytes:
                    raise RuntimeError(f"{name} output file too large: {path.stat().st_size} > {max_bytes} bytes")
            except OSError as exc:
                raise RuntimeError(f"could not stat tau output file: {name}") from exc
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

        if missing_outputs:
            raise RuntimeError(f"tau did not create output file(s): {', '.join(sorted(missing_outputs))}")

    return outputs_by_step


def run_tau_spec_steps_with_trace(
    tau_bin: Optional[str],
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
    if not spec_path.exists():
        raise FileNotFoundError(f"Tau spec not found: {spec_path}")
    if not tau_bin:
        if os.environ.get("TAU_USE_PY_BINDINGS") != "1":
            raise ValueError(
                "tau_bin must be provided (or set TAU_USE_PY_BINDINGS=1 to enable Tau Python bindings fallback)"
            )
        # The Python binding does not (currently) expose the same stdout/stderr REPL traces.
        # Return an empty trace bundle to keep the caller contract stable.
        outputs = _run_tau_spec_steps_via_python_binding(spec_path, steps, timeout_s=timeout_s)
        return outputs, "", "", "(python bindings)"

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
        if has_tau_error_diagnostic(out, err):
            detail = (err or out or "Tau reported an error diagnostic").strip()
            raise TauRunError(
                f"tau reported an error diagnostic (rc=0): {detail[:400]}",
                rc=rc,
                stdout=out,
                stderr=err,
                repl_script=repl_script,
            )

        outputs_by_step: Dict[int, Dict[str, int]] = {}
        missing_outputs: list[str] = []
        for name, path in output_paths.items():
            if not path.exists():
                missing_outputs.append(name)
                continue
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
            except OSError as exc:
                raise TauRunError(
                    f"could not stat tau output file: {name}",
                    rc=rc,
                    stdout=out,
                    stderr=err,
                    repl_script=repl_script,
                ) from exc
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

        if missing_outputs:
            raise TauRunError(
                f"tau did not create output file(s): {', '.join(sorted(missing_outputs))}",
                rc=rc,
                stdout=out,
                stderr=err,
                repl_script=repl_script,
            )

        return outputs_by_step, out, err, repl_script


def run_tau_spec_steps_spec_mode(
    tau_bin: str,
    spec_path: Path,
    steps: List[Dict[str, int]],
    *,
    timeout_s: float = 2.0,
    severity: str = "error",
    experimental: bool = False,
    retry_on_timeout: bool = True,
) -> Dict[int, Dict[str, int]]:
    """
    Run a Tau spec by invoking Tau in file mode (`tau <file>`) and parse stdout.

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
        retry_on_timeout=retry_on_timeout,
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
    retry_on_timeout: bool = True,
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

    tau_bin_path = Path(str(tau_bin)).expanduser()
    if not tau_bin_path.is_absolute():
        # Spec-mode uses a temp working directory, so resolve relative tau paths
        # to the repo root for robustness (mirrors run_tau_spec_steps behavior).
        tau_bin_path = (ROOT / tau_bin_path).resolve()
    else:
        tau_bin_path = tau_bin_path.resolve()
    if not tau_bin_path.exists() or not tau_bin_path.is_file():
        raise FileNotFoundError(f"Tau binary not found: {tau_bin_path}")
    if not os.access(str(tau_bin_path), os.X_OK):
        raise PermissionError(f"Tau binary not executable: {tau_bin_path}")
    tau_bin = str(tau_bin_path)
    if not spec_path.exists():
        raise FileNotFoundError(f"Tau spec not found: {spec_path}")

    raw_spec_text = spec_path.read_text(encoding="utf-8")
    spec_text = normalize_spec_text(raw_spec_text)
    defs = parse_definitions(spec_text)
    always_exprs = extract_always_exprs(spec_text)
    if always_exprs:
        expanded_always_exprs = [inline_definitions(expr, defs) for expr in always_exprs]
        # Tau 0.7 file-runner can reject helper predicate/function definitions that REPL mode accepts.
        # Build a file-runner-safe spec by dropping helper defs and re-emitting inlined always clauses.
        kept_lines: list[str] = []
        skipping_def_block = False
        for raw_line in spec_text.splitlines():
            stripped = raw_line.strip()
            if not stripped:
                continue
            if skipping_def_block:
                if stripped.endswith("."):
                    skipping_def_block = False
                continue
            if re.match(r"^always\b", stripped):
                continue
            if ":=" in stripped and not re.match(r"^[io]\d+\s*:", stripped):
                if not stripped.endswith("."):
                    skipping_def_block = True
                continue
            kept_lines.append(stripped)
        for expr in expanded_always_exprs:
            kept_lines.append(f"always {expr}.")
        spec_text = "\n".join(kept_lines) + "\n"
    stream_types = extract_stream_types(spec_text)
    input_streams = {k: v for k, v in stream_types.items() if k.startswith("i")}
    output_streams = {k: v for k, v in stream_types.items() if k.startswith("o")}
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

    # Tau's file runner is interactive: after consuming the requested values for the
    # last step, it will prompt again. Sending a final blank line terminates cleanly.
    input_text = "\n".join(lines) + "\n\n"

    with tempfile.TemporaryDirectory() as tmpdir:
        tmpdir_path = Path(tmpdir)
        tmp_spec_path = tmpdir_path / spec_path.name
        tmp_spec_path.write_text(spec_text, encoding="utf-8")

        cmd = [tau_bin, str(tmp_spec_path)]
        if experimental:
            cmd.append("--experimental")
        cmd += ["--severity", severity, "--charvar", "false"]

        out_names = sorted(output_streams.keys())
        est_line_bytes = 96
        stdout_budget = 16_384 + len(steps) * max(1, len(out_names)) * est_line_bytes

        # Fail closed: accepting spec-mode output requires both complete outputs and
        # a clean Tau process exit. A non-zero exit may represent a rejected or
        # crashed Tau run after partial output emission.
        attempt_timeouts = [float(timeout_s)]
        if retry_on_timeout and attempt_timeouts[0] < 25.0:
            attempt_timeouts.append(25.0)

        last_rc = -1
        last_out = ""
        last_err = ""
        for attempt_timeout_s in attempt_timeouts:
            rc, out, err = _run_subprocess_with_output_caps(
                cmd,
                input_text=input_text,
                cwd=tmpdir_path,
                timeout_s=float(attempt_timeout_s),
                max_stdout_bytes=min(256_000, max(32_000, int(stdout_budget))),
                max_stderr_bytes=32_000,
            )

            if rc == 0 and has_tau_error_diagnostic(out, err):
                last_rc = rc
                last_out = out
                last_err = err
                break
            try:
                outputs_by_step = _extract_outputs_from_text(out)
            except ValueError as exc:
                last_rc = rc
                last_out = out
                last_err = str(exc)
                break
            if rc == 0 and _outputs_complete(
                outputs_by_step=outputs_by_step,
                out_names=out_names,
                step_count=len(steps),
            ):
                return outputs_by_step, out, err, spec_text, input_text

            last_rc = rc
            last_out = out
            last_err = err
            if (err or "").strip() != "tau timed out":
                break

    detail = (last_err or last_out or "unknown error").strip()
    if last_rc == 0 and has_tau_error_diagnostic(last_out, last_err):
        detail = f"Tau reported an error diagnostic: {detail}"
    raise TauRunError(
        f"tau failed (rc={last_rc}): {detail[:400]}",
        rc=last_rc,
        stdout=last_out,
        stderr=last_err,
        repl_script="",
        mode="spec",
        spec_text=spec_text,
        input_text=input_text,
    )


def split_u32(x: int) -> tuple[int, int]:
    """Split an unsigned 32-bit integer into (hi16, lo16)."""
    if not isinstance(x, int) or isinstance(x, bool) or x < 0 or x > 0xFFFFFFFF:
        raise ValueError(f"Value out of u32 range: {x}")
    return (x >> 16) & 0xFFFF, x & 0xFFFF
