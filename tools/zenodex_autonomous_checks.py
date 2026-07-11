#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import re
import shlex
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]


@dataclass
class CmdResult:
    ok: bool
    timeout: bool
    returncode: int | None
    duration_s: float
    stdout: str
    stderr: str


def _run_cmd(cmd: list[str], *, timeout_s: int, cwd: Path = ROOT, env: dict[str, str] | None = None) -> CmdResult:
    t0 = time.time()
    run_env = dict(os.environ)
    if env:
        run_env.update(env)
    try:
        proc = subprocess.run(
            cmd,
            cwd=str(cwd),
            env=run_env,
            text=True,
            capture_output=True,
            timeout=max(1, int(timeout_s)),
        )
    except subprocess.TimeoutExpired as exc:
        return CmdResult(
            ok=False,
            timeout=True,
            returncode=None,
            duration_s=float(time.time() - t0),
            stdout=str(exc.stdout or ""),
            stderr=str(exc.stderr or ""),
        )
    return CmdResult(
        ok=proc.returncode == 0,
        timeout=False,
        returncode=int(proc.returncode),
        duration_s=float(time.time() - t0),
        stdout=proc.stdout,
        stderr=proc.stderr,
    )


def _extract_json(text: str) -> dict[str, Any] | None:
    s = str(text or "").strip()
    if not s:
        return None
    try:
        obj = json.loads(s)
        return obj if isinstance(obj, dict) else None
    except Exception:
        pass
    for line in reversed(s.splitlines()):
        line = line.strip()
        if not line:
            continue
        try:
            obj = json.loads(line)
            if isinstance(obj, dict):
                return obj
        except Exception:
            continue
    return None


def _mode_status(*, mode: str, signal: bool) -> str:
    if mode == "support":
        return "pass" if signal else "fail"
    if mode == "refute":
        return "pass" if not signal else "fail"
    raise ValueError(f"unsupported mode: {mode}")


def _is_mathlib_wiring_issue(text: str) -> bool:
    err_text = str(text or "").lower()
    mathlib_pkg_missing = ("package directory not found" in err_text and "mathlib" in err_text) or (
        "unknown package" in err_text and "mathlib" in err_text
    )
    mathlib_object_missing = (
        "object file" in err_text
        and "does not exist" in err_text
        and "module mathlib." in err_text
    )
    return bool(mathlib_pkg_missing or mathlib_object_missing)


def _check_pytest_file(mode: str, timeout_s: int, test_path: str) -> dict[str, Any]:
    cmd = ["pytest", "-q", test_path]
    cmd_res = _run_cmd(cmd, timeout_s=timeout_s)
    if cmd_res.timeout:
        return {
            "status": "inconclusive",
            "reason": "timeout",
            "signal": None,
            "counterexample": None,
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    signal = bool(cmd_res.ok)
    counterexample = None if signal else {"pytest_output_tail": (cmd_res.stdout + "\n" + cmd_res.stderr)[-1200:]}
    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": counterexample,
        "metrics": {"returncode": cmd_res.returncode, "test_path": test_path},
        "command": cmd,
        "duration_s": cmd_res.duration_s,
        "stdout_tail": cmd_res.stdout[-1200:],
        "stderr_tail": cmd_res.stderr[-1200:],
    }


def _normalize_pytest_path(raw_path: str) -> str | None:
    path = Path(str(raw_path).strip())
    if path.is_absolute():
        return None
    resolved = (ROOT / path).resolve()
    try:
        rel = resolved.relative_to(ROOT)
    except Exception:
        return None
    if not resolved.exists() or resolved.suffix != ".py":
        return None
    rel_s = str(rel)
    if not rel_s.startswith("tests/"):
        return None
    return rel_s


def _normalize_lean_path(raw_path: str) -> tuple[str, str] | None:
    path = Path(str(raw_path).strip())
    if path.is_absolute():
        return None
    resolved = (ROOT / path).resolve()
    try:
        rel = resolved.relative_to(ROOT)
    except Exception:
        return None
    if not resolved.exists() or resolved.suffix != ".lean":
        return None
    rel_s = str(rel)
    if not rel_s.startswith("lean-mathlib/"):
        return None
    lean_rel = rel_s[len("lean-mathlib/") :]
    if not lean_rel:
        return None
    return rel_s, lean_rel


def _normalize_kernel_yaml(raw_path: str) -> str | None:
    path = Path(str(raw_path).strip())
    if path.is_absolute():
        return None
    resolved = (ROOT / path).resolve()
    try:
        rel = resolved.relative_to(ROOT)
    except Exception:
        return None
    if not resolved.exists() or resolved.suffix != ".yaml":
        return None
    rel_s = str(rel)
    if not rel_s.startswith("src/kernels/"):
        return None
    return rel_s


def _normalize_synth_json(raw_path: str) -> str | None:
    path = Path(str(raw_path).strip())
    if path.is_absolute():
        return None
    resolved = (ROOT / path).resolve()
    try:
        rel = resolved.relative_to(ROOT)
    except Exception:
        return None
    if not resolved.exists() or resolved.suffix != ".json":
        return None
    rel_s = str(rel)
    if not (rel_s.startswith("src/kernels/") or rel_s.startswith("runs/")):
        return None
    return rel_s


_INT_ATOM_RE = re.compile(r"^-?[0-9]+$")
_DIV_OPS = {"div", "mod", "safe_div", "safe_mod"}


def _read_json_dict(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    try:
        obj = json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return None
    return obj if isinstance(obj, dict) else None


def _sexp_tokenize(raw: str) -> list[str]:
    toks: list[str] = []
    buf: list[str] = []
    for ch in str(raw or ""):
        if ch in {"(", ")"}:
            if buf:
                toks.append("".join(buf))
                buf = []
            toks.append(ch)
            continue
        if ch.isspace():
            if buf:
                toks.append("".join(buf))
                buf = []
            continue
        buf.append(ch)
    if buf:
        toks.append("".join(buf))
    return toks


def _parse_sexp(raw: str) -> Any:
    toks = _sexp_tokenize(raw)
    if not toks:
        return None

    def parse_at(i: int) -> tuple[Any, int]:
        if i >= len(toks):
            raise ValueError("unexpected_end")
        tok = toks[i]
        if tok == "(":
            out: list[Any] = []
            j = i + 1
            while j < len(toks) and toks[j] != ")":
                node, j = parse_at(j)
                out.append(node)
            if j >= len(toks) or toks[j] != ")":
                raise ValueError("missing_close")
            return out, j + 1
        if tok == ")":
            raise ValueError("unexpected_close")
        return tok, i + 1

    try:
        node, idx = parse_at(0)
    except Exception:
        return None
    if idx != len(toks):
        return None
    return node


def _grammar_analyze_caps(productions: dict[str, list[str]], start: str) -> dict[str, Any]:
    nts = set(str(k) for k in (productions or {}).keys())
    parsed: dict[str, list[Any]] = {}
    for nt, rows in (productions or {}).items():
        pats: list[Any] = []
        for raw in rows or []:
            s = str(raw or "").strip()
            if not s:
                continue
            node = _parse_sexp(s)
            if node is None:
                node = s
            pats.append(node)
        parsed[str(nt)] = pats

    const_cap = {nt: False for nt in nts}
    div_free_cap = {nt: False for nt in nts}
    d16_safe_cap = {nt: False for nt in nts}
    has_div_cap = {nt: False for nt in nts}

    def atom_is_int(tok: str) -> bool:
        return bool(_INT_ATOM_RE.match(str(tok or "")))

    def eval_const(node: Any, cap: dict[str, bool]) -> bool:
        if isinstance(node, str):
            if node in nts:
                return bool(cap.get(node, False))
            return atom_is_int(node)
        if isinstance(node, list):
            if not node:
                return False
            args = node[1:]
            return all(eval_const(a, cap) for a in args)
        return False

    def eval_div_free(node: Any, cap: dict[str, bool]) -> bool:
        if isinstance(node, str):
            if node in nts:
                return bool(cap.get(node, False))
            return True
        if isinstance(node, list):
            if not node:
                return False
            head = str(node[0]) if node else ""
            if head in _DIV_OPS:
                return False
            return all(eval_div_free(a, cap) for a in node[1:])
        return False

    def eval_has_div(node: Any, cap: dict[str, bool]) -> bool:
        if isinstance(node, str):
            if node in nts:
                return bool(cap.get(node, False))
            return False
        if isinstance(node, list):
            if not node:
                return False
            head = str(node[0]) if node else ""
            if head in _DIV_OPS:
                return True
            return any(eval_has_div(a, cap) for a in node[1:])
        return False

    def eval_d16_safe(node: Any, cap: dict[str, bool], consts: dict[str, bool]) -> bool:
        if isinstance(node, str):
            if node in nts:
                return bool(cap.get(node, False))
            return True
        if isinstance(node, list):
            if not node:
                return False
            head = str(node[0]) if node else ""
            args = node[1:]
            if head in _DIV_OPS:
                if len(args) != 2:
                    return False
                return eval_d16_safe(args[0], cap, consts) and eval_const(args[1], consts)
            return all(eval_d16_safe(a, cap, consts) for a in args)
        return False

    for _ in range(128):
        changed = False
        next_const = dict(const_cap)
        next_div_free = dict(div_free_cap)
        next_d16 = dict(d16_safe_cap)
        next_has_div = dict(has_div_cap)
        for nt in nts:
            pats = parsed.get(nt, [])
            if not next_const[nt] and any(eval_const(p, const_cap) for p in pats):
                next_const[nt] = True
                changed = True
            if not next_div_free[nt] and any(eval_div_free(p, div_free_cap) for p in pats):
                next_div_free[nt] = True
                changed = True
            if not next_d16[nt] and any(eval_d16_safe(p, d16_safe_cap, const_cap) for p in pats):
                next_d16[nt] = True
                changed = True
            if not next_has_div[nt] and any(eval_has_div(p, has_div_cap) for p in pats):
                next_has_div[nt] = True
                changed = True
        const_cap = next_const
        div_free_cap = next_div_free
        d16_safe_cap = next_d16
        has_div_cap = next_has_div
        if not changed:
            break

    start_nt = str(start or "")
    return {
        "start": start_nt,
        "start_exists": start_nt in nts,
        "start_has_div": bool(has_div_cap.get(start_nt, False)),
        "start_div_free": bool(div_free_cap.get(start_nt, False)),
        "start_d16_safe": bool(d16_safe_cap.get(start_nt, False)),
        "start_const": bool(const_cap.get(start_nt, False)),
        "nonterminal_count": len(nts),
    }


def _classify_d16_static(caps: dict[str, Any]) -> str:
    has_div = bool(caps.get("start_has_div", False))
    div_free = bool(caps.get("start_div_free", False))
    d16_safe = bool(caps.get("start_d16_safe", False))
    if not has_div:
        return "no_division"
    if (not div_free) and (not d16_safe):
        return "forced_d16_blocking"
    if (not div_free) and d16_safe:
        return "division_required_but_d16_safe"
    if div_free and (not d16_safe):
        return "div_bypass_possible_nonconst_div"
    if div_free and d16_safe:
        return "div_bypass_and_d16_safe"
    return "other"


def _analyze_synth_d16_static(synth_json: str) -> tuple[dict[str, Any] | None, str]:
    norm_synth = _normalize_synth_json(synth_json)
    if norm_synth is None:
        return None, "invalid_synth_path"
    payload = _read_json_dict(ROOT / norm_synth)
    if payload is None:
        return None, "unreadable_synth_json"

    holes = payload.get("holes")
    grammars = payload.get("grammars")
    if not isinstance(holes, list) or not isinstance(grammars, list):
        return None, "missing_grammar_or_holes"

    grammar_map: dict[str, dict[str, Any]] = {}
    for g in grammars:
        if not isinstance(g, dict):
            continue
        gid = str(g.get("grammar_id", "")).strip()
        if not gid:
            continue
        grammar_map[gid] = g

    hole_rows: list[dict[str, Any]] = []
    for h in holes:
        if not isinstance(h, dict):
            continue
        hid = str(h.get("hole_id", "")).strip()
        gid = str(h.get("grammar_id", "")).strip()
        g = grammar_map.get(gid)
        if g is None:
            hole_rows.append(
                {
                    "hole_id": hid,
                    "grammar_id": gid,
                    "status": "missing_grammar",
                    "class": "other",
                    "caps": {},
                }
            )
            continue
        prods = g.get("productions")
        start = g.get("start")
        if not isinstance(prods, dict) or not isinstance(start, str):
            hole_rows.append(
                {
                    "hole_id": hid,
                    "grammar_id": gid,
                    "status": "bad_grammar_shape",
                    "class": "other",
                    "caps": {},
                }
            )
            continue
        caps = _grammar_analyze_caps({str(k): [str(x) for x in (v or [])] for k, v in prods.items()}, str(start))
        klass = _classify_d16_static(caps)
        hole_rows.append(
            {
                "hole_id": hid,
                "grammar_id": gid,
                "status": "ok",
                "class": klass,
                "caps": caps,
            }
        )

    if not hole_rows:
        return None, "no_holes"

    class_counts: dict[str, int] = {}
    for r in hole_rows:
        k = str(r.get("class", "other"))
        class_counts[k] = int(class_counts.get(k, 0)) + 1

    def c(name: str) -> int:
        return int(class_counts.get(name, 0))

    observed = "other"
    if c("forced_d16_blocking") > 0:
        observed = "forced_d16_blocking"
    elif c("division_required_but_d16_safe") > 0 and c("div_bypass_possible_nonconst_div") == 0 and c("div_bypass_and_d16_safe") == 0:
        observed = "division_required_but_d16_safe"
    elif c("div_bypass_possible_nonconst_div") > 0:
        observed = "div_bypass_possible_nonconst_div"
    elif c("div_bypass_and_d16_safe") > 0:
        observed = "div_bypass_and_d16_safe"
    elif c("no_division") == len(hole_rows):
        observed = "no_division"

    out = {
        "synth_json": norm_synth,
        "observed_static_class": observed,
        "class_counts": class_counts,
        "hole_rows": hole_rows,
        "any_forced": bool(c("forced_d16_blocking") > 0),
    }
    return out, "ok"


def _check_pytest_repeat(mode: str, timeout_s: int, test_path: str, repeats: int) -> dict[str, Any]:
    norm = _normalize_pytest_path(test_path)
    if norm is None:
        return {
            "status": "inconclusive",
            "reason": "invalid_pytest_path",
            "signal": None,
            "counterexample": {"test_path": test_path},
            "metrics": {},
            "command": ["pytest", "-q", test_path],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "invalid pytest path",
        }

    rep = max(1, int(repeats))
    per_timeout = max(1, int(timeout_s) // rep)
    t0 = time.time()
    runs: list[dict[str, Any]] = []
    signal = True
    fail_counterexample: dict[str, Any] | None = None
    for i in range(1, rep + 1):
        row = _check_pytest_file("support", per_timeout, norm)
        runs.append(
            {
                "run_index": i,
                "status": row.get("status"),
                "reason": row.get("reason"),
                "metrics": row.get("metrics"),
                "stdout_tail": row.get("stdout_tail", ""),
                "stderr_tail": row.get("stderr_tail", ""),
            }
        )
        if row.get("status") == "inconclusive":
            return {
                "status": "inconclusive",
                "reason": "repeat_inconclusive",
                "signal": None,
                "counterexample": {"run_index": i, "reason": row.get("reason"), "test_path": norm},
                "metrics": {"repeats": rep, "completed_runs": i - 1},
                "command": ["pytest", "-q", norm],
                "duration_s": float(time.time() - t0),
                "stdout_tail": str(row.get("stdout_tail", ""))[-1200:],
                "stderr_tail": str(row.get("stderr_tail", ""))[-1200:],
            }
        if row.get("status") != "pass":
            signal = False
            fail_counterexample = {
                "run_index": i,
                "reason": row.get("reason"),
                "test_path": norm,
                "metrics": row.get("metrics", {}),
                "stdout_tail": str(row.get("stdout_tail", ""))[-1200:],
                "stderr_tail": str(row.get("stderr_tail", ""))[-1200:],
            }
            break

    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": None if signal else fail_counterexample,
        "metrics": {
            "test_path": norm,
            "repeats": rep,
            "all_runs_passed": signal,
            "runs": [{"run_index": r["run_index"], "status": r["status"]} for r in runs],
        },
        "command": ["pytest", "-q", norm],
        "duration_s": float(time.time() - t0),
        "stdout_tail": "" if not runs else str(runs[-1].get("stdout_tail", ""))[-1200:],
        "stderr_tail": "" if not runs else str(runs[-1].get("stderr_tail", ""))[-1200:],
    }


def _check_lean_file(mode: str, timeout_s: int, lean_path: str) -> dict[str, Any]:
    norm = _normalize_lean_path(lean_path)
    if norm is None:
        return {
            "status": "inconclusive",
            "reason": "invalid_lean_path",
            "signal": None,
            "counterexample": {"lean_path": lean_path},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "invalid lean path",
        }
    rel_repo, lean_rel = norm
    cmd = [
        "bash",
        "-lc",
        f"cd {shlex.quote(str(ROOT / 'lean-mathlib'))} && lake env lean {shlex.quote(lean_rel)}",
    ]
    cmd_res = _run_cmd(cmd, timeout_s=timeout_s)
    if cmd_res.timeout:
        return {
            "status": "inconclusive",
            "reason": "timeout",
            "signal": None,
            "counterexample": {"lean_path": rel_repo},
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    combined = cmd_res.stdout + "\n" + cmd_res.stderr
    # Only classify as wiring issue when Mathlib itself is missing/unavailable.
    if _is_mathlib_wiring_issue(combined):
        return {
            "status": "inconclusive",
            "reason": "mathlib_not_wired",
            "signal": None,
            "counterexample": {"lean_path": rel_repo},
            "metrics": {"returncode": cmd_res.returncode},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    signal = bool(cmd_res.ok)
    counterexample = None
    if not signal:
        counterexample = {"lean_path": rel_repo, "lean_output_tail": (cmd_res.stdout + "\n" + cmd_res.stderr)[-1200:]}
    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": counterexample,
        "metrics": {"lean_path": rel_repo, "returncode": cmd_res.returncode},
        "command": cmd,
        "duration_s": cmd_res.duration_s,
        "stdout_tail": cmd_res.stdout[-1200:],
        "stderr_tail": cmd_res.stderr[-1200:],
    }


def _check_lean_repeat(mode: str, timeout_s: int, lean_path: str, repeats: int) -> dict[str, Any]:
    rep = max(1, int(repeats))
    per_timeout = max(1, int(timeout_s) // rep)
    t0 = time.time()
    runs: list[dict[str, Any]] = []
    signal = True
    fail_counterexample: dict[str, Any] | None = None
    for i in range(1, rep + 1):
        row = _check_lean_file("support", per_timeout, lean_path)
        runs.append(
            {
                "run_index": i,
                "status": row.get("status"),
                "reason": row.get("reason"),
                "metrics": row.get("metrics"),
            }
        )
        if row.get("status") == "inconclusive":
            return {
                "status": "inconclusive",
                "reason": "repeat_inconclusive",
                "signal": None,
                "counterexample": {"run_index": i, "reason": row.get("reason"), "lean_path": lean_path},
                "metrics": {"repeats": rep, "completed_runs": i - 1},
                "command": row.get("command", []),
                "duration_s": float(time.time() - t0),
                "stdout_tail": str(row.get("stdout_tail", ""))[-1200:],
                "stderr_tail": str(row.get("stderr_tail", ""))[-1200:],
            }
        if row.get("status") != "pass":
            signal = False
            fail_counterexample = {
                "run_index": i,
                "reason": row.get("reason"),
                "lean_path": lean_path,
                "metrics": row.get("metrics", {}),
                "stdout_tail": str(row.get("stdout_tail", ""))[-1200:],
                "stderr_tail": str(row.get("stderr_tail", ""))[-1200:],
            }
            break

    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": None if signal else fail_counterexample,
        "metrics": {
            "lean_path": lean_path,
            "repeats": rep,
            "all_runs_passed": signal,
            "runs": [{"run_index": r["run_index"], "status": r["status"]} for r in runs],
        },
        "command": [],
        "duration_s": float(time.time() - t0),
        "stdout_tail": "",
        "stderr_tail": "",
    }


def _check_esso_verify_kernel(
    mode: str,
    timeout_s: int,
    kernel_yaml: str,
    *,
    solvers: str = "cvc5",
    solver_timeout_ms: int = 30000,
    determinism_trials: int = 2,
) -> dict[str, Any]:
    norm = _normalize_kernel_yaml(kernel_yaml)
    if norm is None:
        return {
            "status": "inconclusive",
            "reason": "invalid_kernel_path",
            "signal": None,
            "counterexample": {"kernel_yaml": kernel_yaml},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "invalid kernel path",
        }
    solver_list = str(solvers or "").strip()
    if not solver_list or not re.fullmatch(r"[A-Za-z0-9_,.-]+", solver_list):
        return {
            "status": "inconclusive",
            "reason": "invalid_solver_list",
            "signal": None,
            "counterexample": {"kernel_yaml": norm, "solvers": solvers},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "invalid solver list",
        }
    timeout_ms = int(solver_timeout_ms)
    if timeout_ms <= 0:
        return {
            "status": "inconclusive",
            "reason": "invalid_solver_timeout_ms",
            "signal": None,
            "counterexample": {"kernel_yaml": norm, "solver_timeout_ms": timeout_ms},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "invalid solver timeout",
        }
    det_trials = max(1, int(determinism_trials))
    cmd = [
        "bash",
        "-lc",
        (
            "cd "
            + shlex.quote(str(ROOT))
            + " && PYTHONPATH=external/ESSO python3 -m ESSO verify-multi "
            + shlex.quote(norm)
            + " --solvers "
            + shlex.quote(solver_list)
            + " --timeout-ms "
            + str(timeout_ms)
            + " --determinism-trials "
            + str(det_trials)
        ),
    ]
    cmd_res = _run_cmd(cmd, timeout_s=timeout_s)
    if cmd_res.timeout:
        return {
            "status": "inconclusive",
            "reason": "timeout",
            "signal": None,
            "counterexample": {"kernel_yaml": norm},
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    payload = _extract_json(cmd_res.stdout)
    if payload is None:
        return {
            "status": "inconclusive",
            "reason": "unparseable_json",
            "signal": None,
            "counterexample": {"kernel_yaml": norm},
            "metrics": {"returncode": cmd_res.returncode},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    verdict = str((payload.get("report") or {}).get("verdict", ""))
    signal = bool(cmd_res.ok and payload.get("ok") is True and verdict == "VERIFIED")
    counterexample = None if signal else {"kernel_yaml": norm, "verify_report": payload}
    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": counterexample,
        "metrics": {
            "kernel_yaml": norm,
            "verdict": verdict,
            "ok": payload.get("ok"),
            "solvers": solver_list,
            "solver_timeout_ms": timeout_ms,
            "determinism_trials": det_trials,
        },
        "command": cmd,
        "duration_s": cmd_res.duration_s,
        "stdout_tail": cmd_res.stdout[-1200:],
        "stderr_tail": cmd_res.stderr[-1200:],
    }


def _check_esso_repeat(
    mode: str,
    timeout_s: int,
    kernel_yaml: str,
    repeats: int,
    *,
    solvers: str = "cvc5",
    solver_timeout_ms: int = 30000,
    determinism_trials: int = 2,
) -> dict[str, Any]:
    rep = max(1, int(repeats))
    per_timeout = max(1, int(timeout_s) // rep)
    t0 = time.time()
    runs: list[dict[str, Any]] = []
    signal = True
    fail_counterexample: dict[str, Any] | None = None
    for i in range(1, rep + 1):
        row = _check_esso_verify_kernel(
            "support",
            per_timeout,
            kernel_yaml,
            solvers=solvers,
            solver_timeout_ms=solver_timeout_ms,
            determinism_trials=determinism_trials,
        )
        runs.append({"run_index": i, "status": row.get("status"), "reason": row.get("reason"), "metrics": row.get("metrics")})
        if row.get("status") == "inconclusive":
            return {
                "status": "inconclusive",
                "reason": "repeat_inconclusive",
                "signal": None,
                "counterexample": {"run_index": i, "reason": row.get("reason"), "kernel_yaml": kernel_yaml},
                "metrics": {"repeats": rep, "completed_runs": i - 1},
                "command": row.get("command", []),
                "duration_s": float(time.time() - t0),
                "stdout_tail": str(row.get("stdout_tail", ""))[-1200:],
                "stderr_tail": str(row.get("stderr_tail", ""))[-1200:],
            }
        if row.get("status") != "pass":
            signal = False
            fail_counterexample = {
                "run_index": i,
                "reason": row.get("reason"),
                "kernel_yaml": kernel_yaml,
                "metrics": row.get("metrics", {}),
                "stdout_tail": str(row.get("stdout_tail", ""))[-1200:],
                "stderr_tail": str(row.get("stderr_tail", ""))[-1200:],
            }
            break
    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": None if signal else fail_counterexample,
        "metrics": {
            "kernel_yaml": kernel_yaml,
            "repeats": rep,
            "all_runs_passed": signal,
            "solvers": str(solvers),
            "solver_timeout_ms": int(solver_timeout_ms),
            "determinism_trials": int(max(1, int(determinism_trials))),
            "runs": [{"run_index": r["run_index"], "status": r["status"]} for r in runs],
        },
        "command": [],
        "duration_s": float(time.time() - t0),
        "stdout_tail": "",
        "stderr_tail": "",
    }


def _check_esso_synth(
    mode: str,
    timeout_s: int,
    model_yaml: str,
    synth_json: str,
    *,
    solvers: str = "cvc5",
    solver_timeout_ms: int = 10000,
    max_iters: int = 12,
    ce_suite_max_size: int = 24,
) -> dict[str, Any]:
    norm_model = _normalize_kernel_yaml(model_yaml)
    norm_synth = _normalize_synth_json(synth_json)
    if norm_model is None:
        return {
            "status": "inconclusive",
            "reason": "invalid_model_path",
            "signal": None,
            "counterexample": {"model_yaml": model_yaml},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "invalid model path",
        }
    if norm_synth is None:
        return {
            "status": "inconclusive",
            "reason": "invalid_synth_path",
            "signal": None,
            "counterexample": {"synth_json": synth_json},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "invalid synth path",
        }
    solver_list = str(solvers or "").strip()
    if not solver_list or not re.fullmatch(r"[A-Za-z0-9_,.-]+", solver_list):
        return {
            "status": "inconclusive",
            "reason": "invalid_solver_list",
            "signal": None,
            "counterexample": {"model_yaml": norm_model, "synth_json": norm_synth, "solvers": solvers},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "invalid solver list",
        }
    timeout_ms = int(solver_timeout_ms)
    if timeout_ms <= 0:
        return {
            "status": "inconclusive",
            "reason": "invalid_solver_timeout_ms",
            "signal": None,
            "counterexample": {"model_yaml": norm_model, "synth_json": norm_synth, "solver_timeout_ms": timeout_ms},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "invalid solver timeout",
        }

    run_dir = Path(tempfile.mkdtemp(prefix="zenodex_esso_synth_", dir="/tmp"))
    cmd = [
        "bash",
        "-lc",
        (
            "cd "
            + shlex.quote(str(ROOT))
            + " && python3 -m ESSO synth "
            + shlex.quote(norm_model)
            + " "
            + shlex.quote(norm_synth)
            + " --profile dev --solvers "
            + shlex.quote(solver_list)
            + " --timeout-ms "
            + str(timeout_ms)
            + " --determinism-trials 1 --max-iters "
            + str(max(1, int(max_iters)))
            + " --ce-suite-max-size "
            + str(max(1, int(ce_suite_max_size)))
            + " --output "
            + shlex.quote(str(run_dir))
        ),
    ]
    cmd_res = _run_cmd(cmd, timeout_s=timeout_s)
    if cmd_res.timeout:
        return {
            "status": "inconclusive",
            "reason": "timeout",
            "signal": None,
            "counterexample": {"model_yaml": norm_model, "synth_json": norm_synth},
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }

    payload = None
    result_path = run_dir / "result.json"
    if result_path.exists():
        try:
            cand = json.loads(result_path.read_text(encoding="utf-8"))
            if isinstance(cand, dict):
                payload = cand
        except Exception:
            payload = None
    if payload is None:
        payload = _extract_json(cmd_res.stdout)
    if payload is None:
        return {
            "status": "inconclusive",
            "reason": "unparseable_json",
            "signal": None,
            "counterexample": {"model_yaml": norm_model, "synth_json": norm_synth},
            "metrics": {"returncode": cmd_res.returncode},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }

    label = str(payload.get("label", ""))
    ok_flag = bool(payload.get("ok") is True)
    # ESSO synth success labels can be VERIFIED_* variants (e.g., VERIFIED_SINGLE_SOLVER).
    signal = bool(ok_flag)
    counterexample = None if signal else {"synth_result": payload}
    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": counterexample,
        "metrics": {
            "model_yaml": norm_model,
            "synth_json": norm_synth,
            "ok": payload.get("ok"),
            "label": label,
            "exit_code": payload.get("exit_code"),
            "solvers": solver_list,
            "solver_timeout_ms": timeout_ms,
        },
        "command": cmd,
        "duration_s": cmd_res.duration_s,
        "stdout_tail": cmd_res.stdout[-1200:],
        "stderr_tail": cmd_res.stderr[-1200:],
    }


def _expr_summary(expr: Any) -> dict[str, Any]:
    node_count = 0
    max_depth = 0
    const_count = 0
    const_values: set[int] = set()
    vars_seen: set[str] = set()
    ops_seen: set[str] = set()

    def walk(node: Any, depth: int) -> None:
        nonlocal node_count, max_depth, const_count
        node_count += 1
        max_depth = max(max_depth, depth)
        if isinstance(node, dict):
            if set(node.keys()) == {"const"}:
                const_count += 1
                try:
                    const_values.add(int(node.get("const")))
                except Exception:
                    pass
                return
            if set(node.keys()) == {"var"}:
                v = node.get("var")
                if isinstance(v, str):
                    vars_seen.add(v)
                return
            if set(node.keys()) == {"param"}:
                v = node.get("param")
                if isinstance(v, str):
                    vars_seen.add(v)
                return
            op = node.get("op")
            args = node.get("args")
            if isinstance(op, str):
                ops_seen.add(str(op))
            if isinstance(args, list):
                for item in args:
                    walk(item, depth + 1)
            elif args is not None:
                walk(args, depth + 1)
            for k, v in node.items():
                if str(k) in {"const", "var", "param", "op", "args"}:
                    continue
                walk(v, depth + 1)
            return
        if isinstance(node, list):
            for item in node:
                walk(item, depth + 1)

    walk(expr, 1)
    return {
        "node_count": int(node_count),
        "max_depth": int(max_depth),
        "const_count": int(const_count),
        "const_values": sorted(const_values),
        "var_count": int(len(vars_seen)),
        "vars": sorted(vars_seen),
        "ops": sorted(ops_seen),
    }


def _is_const_atom(expr: Any) -> bool:
    return isinstance(expr, dict) and set(expr.keys()) == {"const"}


def _normalize_op_name(name: str) -> str:
    n = str(name or "").strip().lower()
    alias = {
        "mul": "*",
        "add": "+",
        "sub": "-",
        "div": "/",
    }
    return alias.get(n, n)


def _eval_expr_predicate(expr: Any, predicate: str) -> tuple[bool, dict[str, Any]]:
    pred = str(predicate or "").strip().lower()
    summary = _expr_summary(expr)
    ops = set(str(x) for x in summary.get("ops", []))
    norm_ops = set(_normalize_op_name(x) for x in ops) | ops
    var_count = int(summary.get("var_count", 0))
    node_count = int(summary.get("node_count", 0))
    const_values = set(int(x) for x in summary.get("const_values", []) if isinstance(x, int))

    if pred == "is_const_atom":
        return (_is_const_atom(expr), summary)
    if pred == "const_zero":
        if _is_const_atom(expr):
            try:
                return (int((expr or {}).get("const", 1)) == 0, summary)
            except Exception:
                return (False, summary)
        return (False, summary)
    if pred == "non_const":
        return (not _is_const_atom(expr), summary)
    if pred == "has_var":
        return (var_count > 0, summary)
    if pred == "nontrivial":
        return (not _is_const_atom(expr) and var_count > 0 and node_count >= 4 and len(norm_ops) >= 1, summary)
    if pred == "cpmm_rational_shape":
        has_mul = "*" in norm_ops
        has_add = "+" in norm_ops
        has_div = "safe_div" in norm_ops or "/" in norm_ops
        return (has_mul and has_add and has_div and var_count >= 2, summary)
    if pred.startswith("contains_op_"):
        op_raw = pred[len("contains_op_") :]
        op = _normalize_op_name(op_raw)
        return (op in norm_ops or op_raw in norm_ops, summary)
    if pred.startswith("min_nodes_"):
        try:
            n = int(pred[len("min_nodes_") :])
        except Exception:
            return (False, summary)
        return (node_count >= max(1, n), summary)
    if pred.startswith("contains_const_"):
        raw = pred[len("contains_const_") :]
        try:
            c = int(raw)
        except Exception:
            return (False, summary)
        return (c in const_values, summary)
    return (False, summary)


def _extract_target_expr(filled_holes: Any, hole_id: str) -> tuple[Any | None, str]:
    if not isinstance(filled_holes, dict):
        return (None, "missing_filled_holes")
    if hole_id == "*":
        if len(filled_holes) == 1:
            only = next(iter(filled_holes.values()))
            return (only, "ok")
        return (None, "ambiguous_wildcard_hole")
    if hole_id in filled_holes:
        return (filled_holes[hole_id], "ok")
    if len(filled_holes) == 1:
        only = next(iter(filled_holes.values()))
        return (only, "single_hole_fallback")
    return (None, "missing_hole")


def _coerce_bool(v: Any) -> bool:
    if isinstance(v, bool):
        return v
    if isinstance(v, (int, float)):
        return int(v) != 0
    if isinstance(v, str):
        return v.strip().lower() in {"1", "true", "t", "yes"}
    return bool(v)


def _coerce_int(v: Any) -> int:
    if isinstance(v, bool):
        return 1 if v else 0
    if isinstance(v, (int, float)):
        return int(v)
    if isinstance(v, str):
        try:
            return int(v.strip())
        except Exception:
            return 0
    return 0


def _eval_expr_runtime(node: Any, env: dict[str, int]) -> Any:
    if isinstance(node, dict):
        if "const" in node and len(node) == 1:
            return _coerce_int(node.get("const"))
        if "var" in node and len(node) == 1:
            return _coerce_int(env.get(str(node.get("var")), 0))
        if "param" in node and len(node) == 1:
            return _coerce_int(env.get(str(node.get("param")), 0))
        if all(k in node for k in ("cond", "then", "else")):
            return _eval_expr_runtime(node.get("then"), env) if _coerce_bool(_eval_expr_runtime(node.get("cond"), env)) else _eval_expr_runtime(node.get("else"), env)
        op = str(node.get("op", ""))
        args = node.get("args", [])
        av = [_eval_expr_runtime(a, env) for a in (args if isinstance(args, list) else [args])]
        if op in {"+", "add"}:
            return sum(_coerce_int(x) for x in av)
        if op in {"-", "sub"}:
            if not av:
                return 0
            if len(av) == 1:
                return -_coerce_int(av[0])
            out = _coerce_int(av[0])
            for x in av[1:]:
                out -= _coerce_int(x)
            return out
        if op in {"*", "mul"}:
            out = 1
            for x in av:
                out *= _coerce_int(x)
            return out
        if op in {"div", "safe_div"}:
            if len(av) != 2:
                return 0
            a = _coerce_int(av[0])
            b = _coerce_int(av[1])
            if b == 0:
                return 0
            return int(a // b)
        if op in {"mod", "safe_mod"}:
            if len(av) != 2:
                return 0
            a = _coerce_int(av[0])
            b = _coerce_int(av[1])
            if b == 0:
                return 0
            return int(a % b)
        if op in {"<", "<=", ">", ">=", "=", "==", "!="}:
            if len(av) != 2:
                return False
            a = _coerce_int(av[0])
            b = _coerce_int(av[1])
            if op == "<":
                return a < b
            if op == "<=":
                return a <= b
            if op == ">":
                return a > b
            if op == ">=":
                return a >= b
            if op in {"=", "=="}:
                return a == b
            return a != b
        if op in {"and", "or", "xor"}:
            if op == "and":
                return all(_coerce_bool(x) for x in av)
            if op == "or":
                return any(_coerce_bool(x) for x in av)
            out = False
            for x in av:
                out = bool(out) ^ bool(_coerce_bool(x))
            return out
        if op == "not":
            return not _coerce_bool(av[0]) if av else True
        if op == "ite":
            if len(av) != 3:
                return 0
            return av[1] if _coerce_bool(av[0]) else av[2]
        return 0
    if isinstance(node, list):
        if not node:
            return 0
        if isinstance(node[0], str):
            # Minimal S-expression support for odd payloads.
            head = node[0]
            args = [{"op": head, "args": node[1:]}]
            return _eval_expr_runtime(args[0], env)
        return _eval_expr_runtime(node[0], env)
    return _coerce_int(node)


def _inspect_sygus_grammar_shape(run_dir: Path) -> dict[str, Any]:
    try:
        p = run_dir / "artifacts" / "sygus" / "iter_001" / "sygus_problem.smt2"
    except Exception:
        return {
            "has_synth_fun": False,
            "grammar_embedded": False,
            "signature_line": "",
            "reason": "bad_run_dir",
        }
    if not p.exists():
        return {
            "has_synth_fun": False,
            "grammar_embedded": False,
            "signature_line": "",
            "reason": "missing_sygus_problem",
        }
    try:
        lines = p.read_text(encoding="utf-8").splitlines()
    except Exception:
        return {
            "has_synth_fun": False,
            "grammar_embedded": False,
            "signature_line": "",
            "reason": "read_error",
        }
    sig_line = ""
    for ln in lines:
        if "(synth-fun" in ln:
            sig_line = ln.strip()
            break
    if not sig_line:
        return {
            "has_synth_fun": False,
            "grammar_embedded": False,
            "signature_line": "",
            "reason": "missing_synth_fun",
        }
    no_grammar = bool(re.search(r"\bInt\s*\)\s*$", sig_line))
    with_grammar = bool(re.search(r"\bInt\s*\(", sig_line))
    grammar_embedded = bool(with_grammar and not no_grammar)
    if not with_grammar and not no_grammar:
        # Fallback for multiline shape: inspect local window.
        idx = lines.index(ln) if ln in lines else -1
        window = "\n".join(lines[max(0, idx) : min(len(lines), idx + 6)])
        grammar_embedded = "((" in window and "synth-fun" in window
    return {
        "has_synth_fun": True,
        "grammar_embedded": bool(grammar_embedded),
        "signature_line": sig_line[:500],
        "reason": "ok",
    }


def _check_esso_synth_nontrivial(
    mode: str,
    timeout_s: int,
    model_yaml: str,
    synth_json: str,
    hole_id: str,
    predicate: str,
    *,
    solvers: str = "cvc5",
    solver_timeout_ms: int = 10000,
    max_iters: int = 20,
    ce_suite_max_size: int = 64,
) -> dict[str, Any]:
    norm_model = _normalize_kernel_yaml(model_yaml)
    norm_synth = _normalize_synth_json(synth_json)
    if norm_model is None:
        return {
            "status": "inconclusive",
            "reason": "invalid_model_path",
            "signal": None,
            "counterexample": {"model_yaml": model_yaml},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "invalid model path",
        }
    if norm_synth is None:
        return {
            "status": "inconclusive",
            "reason": "invalid_synth_path",
            "signal": None,
            "counterexample": {"synth_json": synth_json},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "invalid synth path",
        }
    solver_list = str(solvers or "").strip()
    if not solver_list or not re.fullmatch(r"[A-Za-z0-9_,.-]+", solver_list):
        return {
            "status": "inconclusive",
            "reason": "invalid_solver_list",
            "signal": None,
            "counterexample": {"model_yaml": norm_model, "synth_json": norm_synth, "solvers": solvers},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "invalid solver list",
        }
    timeout_ms = int(solver_timeout_ms)
    if timeout_ms <= 0:
        return {
            "status": "inconclusive",
            "reason": "invalid_solver_timeout_ms",
            "signal": None,
            "counterexample": {"model_yaml": norm_model, "synth_json": norm_synth, "solver_timeout_ms": timeout_ms},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "invalid solver timeout",
        }
    target_hole = str(hole_id or "").strip()
    if not target_hole:
        return {
            "status": "inconclusive",
            "reason": "invalid_hole_id",
            "signal": None,
            "counterexample": {"hole_id": hole_id},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "invalid hole id",
        }
    pred = str(predicate or "").strip()
    if not re.fullmatch(r"[A-Za-z0-9_.*+\-]+", pred):
        return {
            "status": "inconclusive",
            "reason": "invalid_predicate",
            "signal": None,
            "counterexample": {"predicate": predicate},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "invalid predicate",
        }

    run_dir = Path(tempfile.mkdtemp(prefix="zenodex_esso_nontrivial_", dir="/tmp"))
    max_iters_i = max(1, int(max_iters))
    ce_suite_i = max(1, int(ce_suite_max_size))
    cmd = [
        "bash",
        "-lc",
        (
            "cd "
            + shlex.quote(str(ROOT))
            + " && python3 -m ESSO synth "
            + shlex.quote(norm_model)
            + " "
            + shlex.quote(norm_synth)
            + " --profile dev --solvers "
            + shlex.quote(solver_list)
            + " --timeout-ms "
            + str(timeout_ms)
            + " --determinism-trials 1 --max-iters "
            + str(max_iters_i)
            + " --ce-suite-max-size "
            + str(ce_suite_i)
            + " --portfolio-enum-max-cost 80 --portfolio-enum-max-terms-per-hole 512 --portfolio-enum-max-attempts 300"
            + " --portfolio-mcts-rollouts 200 --portfolio-mcts-max-cost 80 --portfolio-mcts-max-terms-per-hole 128"
            + " --output "
            + shlex.quote(str(run_dir))
        ),
    ]
    cmd_res = _run_cmd(cmd, timeout_s=timeout_s)
    if cmd_res.timeout:
        return {
            "status": "inconclusive",
            "reason": "timeout",
            "signal": None,
            "counterexample": {"model_yaml": norm_model, "synth_json": norm_synth},
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }

    payload = None
    result_path = run_dir / "result.json"
    if result_path.exists():
        try:
            cand = json.loads(result_path.read_text(encoding="utf-8"))
            if isinstance(cand, dict):
                payload = cand
        except Exception:
            payload = None
    if payload is None:
        payload = _extract_json(cmd_res.stdout)
    if payload is None:
        return {
            "status": "inconclusive",
            "reason": "unparseable_json",
            "signal": None,
            "counterexample": {"model_yaml": norm_model, "synth_json": norm_synth},
            "metrics": {"returncode": cmd_res.returncode},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }

    ok_flag = bool(payload.get("ok") is True)
    label = str(payload.get("label", ""))
    filled_holes = payload.get("filled_holes")
    grammar_shape = _inspect_sygus_grammar_shape(run_dir)
    err = payload.get("error")
    err_obj = err if isinstance(err, dict) else {}
    err_msg = str(err_obj.get("message", ""))
    expr, extract_reason = _extract_target_expr(filled_holes, target_hole)
    expr_summary: dict[str, Any] = {}
    if not ok_flag:
        return {
            "status": "inconclusive",
            "reason": "synth_no_candidate",
            "signal": None,
            "counterexample": {
                "model_yaml": norm_model,
                "synth_json": norm_synth,
                "hole_id": target_hole,
                "predicate": pred,
                "synth_result": payload,
                "error_message": err_msg,
            },
            "metrics": {
                "model_yaml": norm_model,
                "synth_json": norm_synth,
                "hole_id": target_hole,
                "predicate": pred,
                "ok": ok_flag,
                "label": label,
                "error_message": err_msg,
                "solvers": solver_list,
                "solver_timeout_ms": timeout_ms,
                "max_iters": max_iters_i,
                "ce_suite_max_size": ce_suite_i,
                "sygus_has_synth_fun": bool(grammar_shape.get("has_synth_fun")),
                "sygus_grammar_embedded": bool(grammar_shape.get("grammar_embedded")),
                "sygus_signature_line": str(grammar_shape.get("signature_line", "")),
            },
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }

    signal = False
    if expr is not None:
        signal, expr_summary = _eval_expr_predicate(expr, pred)
    else:
        signal = False

    counterexample = None
    if not signal:
        counterexample = {
            "model_yaml": norm_model,
            "synth_json": norm_synth,
            "hole_id": target_hole,
            "predicate": pred,
            "extract_reason": extract_reason,
            "filled_holes": filled_holes,
            "expr": expr,
            "expr_summary": expr_summary,
            "sygus_grammar": grammar_shape,
            "synth_result": payload,
        }
    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": counterexample,
        "metrics": {
            "model_yaml": norm_model,
            "synth_json": norm_synth,
            "hole_id": target_hole,
            "predicate": pred,
            "ok": ok_flag,
            "label": label,
            "exit_code": payload.get("exit_code"),
            "extract_reason": extract_reason,
            "expr_summary": expr_summary,
            "sygus_has_synth_fun": bool(grammar_shape.get("has_synth_fun")),
            "sygus_grammar_embedded": bool(grammar_shape.get("grammar_embedded")),
            "sygus_signature_line": str(grammar_shape.get("signature_line", "")),
            "solvers": solver_list,
            "solver_timeout_ms": timeout_ms,
            "max_iters": max_iters_i,
            "ce_suite_max_size": ce_suite_i,
        },
        "command": cmd,
        "duration_s": cmd_res.duration_s,
        "stdout_tail": cmd_res.stdout[-1200:],
        "stderr_tail": cmd_res.stderr[-1200:],
    }


def _check_esso_sygus_grammar_embedded(
    mode: str,
    timeout_s: int,
    model_yaml: str,
    synth_json: str,
    *,
    solvers: str = "cvc5",
    solver_timeout_ms: int = 10000,
    max_iters: int = 12,
    ce_suite_max_size: int = 24,
) -> dict[str, Any]:
    norm_model = _normalize_kernel_yaml(model_yaml)
    norm_synth = _normalize_synth_json(synth_json)
    if norm_model is None:
        return {
            "status": "inconclusive",
            "reason": "invalid_model_path",
            "signal": None,
            "counterexample": {"model_yaml": model_yaml},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "invalid model path",
        }
    if norm_synth is None:
        return {
            "status": "inconclusive",
            "reason": "invalid_synth_path",
            "signal": None,
            "counterexample": {"synth_json": synth_json},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "invalid synth path",
        }
    solver_list = str(solvers or "").strip()
    if not solver_list or not re.fullmatch(r"[A-Za-z0-9_,.-]+", solver_list):
        return {
            "status": "inconclusive",
            "reason": "invalid_solver_list",
            "signal": None,
            "counterexample": {"model_yaml": norm_model, "synth_json": norm_synth, "solvers": solvers},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "invalid solver list",
        }
    timeout_ms = int(solver_timeout_ms)
    if timeout_ms <= 0:
        return {
            "status": "inconclusive",
            "reason": "invalid_solver_timeout_ms",
            "signal": None,
            "counterexample": {"model_yaml": norm_model, "synth_json": norm_synth, "solver_timeout_ms": timeout_ms},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "invalid solver timeout",
        }

    run_dir = Path(tempfile.mkdtemp(prefix="zenodex_esso_grammar_", dir="/tmp"))
    cmd = [
        "bash",
        "-lc",
        (
            "cd "
            + shlex.quote(str(ROOT))
            + " && python3 -m ESSO synth "
            + shlex.quote(norm_model)
            + " "
            + shlex.quote(norm_synth)
            + " --profile dev --solvers "
            + shlex.quote(solver_list)
            + " --timeout-ms "
            + str(timeout_ms)
            + " --determinism-trials 1 --max-iters "
            + str(max(1, int(max_iters)))
            + " --ce-suite-max-size "
            + str(max(1, int(ce_suite_max_size)))
            + " --output "
            + shlex.quote(str(run_dir))
        ),
    ]
    cmd_res = _run_cmd(cmd, timeout_s=timeout_s)
    if cmd_res.timeout:
        return {
            "status": "inconclusive",
            "reason": "timeout",
            "signal": None,
            "counterexample": {"model_yaml": norm_model, "synth_json": norm_synth},
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }

    shape = _inspect_sygus_grammar_shape(run_dir)
    has_synth_fun = bool(shape.get("has_synth_fun"))
    grammar_embedded = bool(shape.get("grammar_embedded"))
    signal = bool(has_synth_fun and grammar_embedded)
    counterexample = None
    if not signal:
        counterexample = {
            "model_yaml": norm_model,
            "synth_json": norm_synth,
            "shape": shape,
        }
    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": counterexample,
        "metrics": {
            "model_yaml": norm_model,
            "synth_json": norm_synth,
            "solvers": solver_list,
            "solver_timeout_ms": timeout_ms,
            "has_synth_fun": has_synth_fun,
            "grammar_embedded": grammar_embedded,
            "signature_line": str(shape.get("signature_line", "")),
        },
        "command": cmd,
        "duration_s": cmd_res.duration_s,
        "stdout_tail": cmd_res.stdout[-1200:],
        "stderr_tail": cmd_res.stderr[-1200:],
    }


def _check_esso_qsygus_terms_min(
    mode: str,
    timeout_s: int,
    model_yaml: str,
    synth_json: str,
    min_terms: int,
    *,
    solvers: str = "cvc5",
    solver_timeout_ms: int = 6000,
) -> dict[str, Any]:
    norm_model = _normalize_kernel_yaml(model_yaml)
    norm_synth = _normalize_synth_json(synth_json)
    if norm_model is None:
        return {
            "status": "inconclusive",
            "reason": "invalid_model_path",
            "signal": None,
            "counterexample": {"model_yaml": model_yaml},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "invalid model path",
        }
    if norm_synth is None:
        return {
            "status": "inconclusive",
            "reason": "invalid_synth_path",
            "signal": None,
            "counterexample": {"synth_json": synth_json},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "invalid synth path",
        }
    solver_list = str(solvers or "").strip()
    if not solver_list or not re.fullmatch(r"[A-Za-z0-9_,.-]+", solver_list):
        return {
            "status": "inconclusive",
            "reason": "invalid_solver_list",
            "signal": None,
            "counterexample": {"model_yaml": norm_model, "synth_json": norm_synth, "solvers": solvers},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "invalid solver list",
        }
    timeout_ms = int(solver_timeout_ms)
    if timeout_ms <= 0:
        return {
            "status": "inconclusive",
            "reason": "invalid_solver_timeout_ms",
            "signal": None,
            "counterexample": {"model_yaml": norm_model, "synth_json": norm_synth, "solver_timeout_ms": timeout_ms},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "invalid solver timeout",
        }
    min_terms_i = max(0, int(min_terms))

    run_dir = Path(tempfile.mkdtemp(prefix="zenodex_esso_qsygus_", dir="/tmp"))
    cmd = [
        "bash",
        "-lc",
        (
            "cd "
            + shlex.quote(str(ROOT))
            + " && python3 -m ESSO synth "
            + shlex.quote(norm_model)
            + " "
            + shlex.quote(norm_synth)
            + " --profile dev --solvers "
            + shlex.quote(solver_list)
            + " --timeout-ms "
            + str(timeout_ms)
            + " --determinism-trials 1 --max-iters 20 --ce-suite-max-size 64"
            + " --portfolio-enum-max-cost 80 --portfolio-enum-max-terms-per-hole 512 --portfolio-enum-max-attempts 300"
            + " --portfolio-mcts-rollouts 200 --portfolio-mcts-max-cost 80 --portfolio-mcts-max-terms-per-hole 128"
            + " --output "
            + shlex.quote(str(run_dir))
        ),
    ]
    cmd_res = _run_cmd(cmd, timeout_s=timeout_s)
    if cmd_res.timeout:
        return {
            "status": "inconclusive",
            "reason": "timeout",
            "signal": None,
            "counterexample": {"model_yaml": norm_model, "synth_json": norm_synth},
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }

    meta_path = run_dir / "artifacts" / "meta.json"
    meta = None
    if meta_path.exists():
        try:
            obj = json.loads(meta_path.read_text(encoding="utf-8"))
            if isinstance(obj, dict):
                meta = obj
        except Exception:
            meta = None
    if meta is None:
        return {
            "status": "inconclusive",
            "reason": "missing_meta",
            "signal": None,
            "counterexample": {"model_yaml": norm_model, "synth_json": norm_synth},
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }

    portfolio = meta.get("portfolio") if isinstance(meta, dict) else {}
    enum_block = portfolio.get("enum") if isinstance(portfolio, dict) else {}
    metrics = enum_block.get("metrics") if isinstance(enum_block, dict) else {}
    terms_total = int((metrics or {}).get("terms_generated_total", 0) or 0)
    signal = bool(terms_total >= min_terms_i)
    counterexample = None
    if not signal:
        counterexample = {
            "model_yaml": norm_model,
            "synth_json": norm_synth,
            "terms_generated_total": terms_total,
            "min_terms": min_terms_i,
            "enum_metrics": metrics,
        }
    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": counterexample,
        "metrics": {
            "model_yaml": norm_model,
            "synth_json": norm_synth,
            "solvers": solver_list,
            "solver_timeout_ms": timeout_ms,
            "min_terms": min_terms_i,
            "terms_generated_total": terms_total,
            "enum_ok": bool((enum_block or {}).get("ok")),
        },
        "command": cmd,
        "duration_s": cmd_res.duration_s,
        "stdout_tail": cmd_res.stdout[-1200:],
        "stderr_tail": cmd_res.stderr[-1200:],
    }


def _check_esso_cpmm_quality_min_mean_ppm(
    mode: str,
    timeout_s: int,
    model_yaml: str,
    synth_json: str,
    *,
    min_mean_ppm: int,
    samples: int,
    solvers: str = "cvc5",
    solver_timeout_ms: int = 6000,
) -> dict[str, Any]:
    norm_model = _normalize_kernel_yaml(model_yaml)
    norm_synth = _normalize_synth_json(synth_json)
    if norm_model is None:
        return {
            "status": "inconclusive",
            "reason": "invalid_model_path",
            "signal": None,
            "counterexample": {"model_yaml": model_yaml},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "invalid model path",
        }
    if norm_synth is None:
        return {
            "status": "inconclusive",
            "reason": "invalid_synth_path",
            "signal": None,
            "counterexample": {"synth_json": synth_json},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "invalid synth path",
        }

    solver_list = str(solvers or "").strip()
    if not solver_list or not re.fullmatch(r"[A-Za-z0-9_,.-]+", solver_list):
        return {
            "status": "inconclusive",
            "reason": "invalid_solver_list",
            "signal": None,
            "counterexample": {"solvers": solvers},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "invalid solver list",
        }
    timeout_ms = int(solver_timeout_ms)
    if timeout_ms <= 0:
        return {
            "status": "inconclusive",
            "reason": "invalid_solver_timeout_ms",
            "signal": None,
            "counterexample": {"solver_timeout_ms": timeout_ms},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "invalid solver timeout",
        }
    min_ppm_i = max(0, int(min_mean_ppm))
    sample_n = max(1, int(samples))

    run_dir = Path(tempfile.mkdtemp(prefix="zenodex_esso_cpmm_q_", dir="/tmp"))
    cmd = [
        "bash",
        "-lc",
        (
            "cd "
            + shlex.quote(str(ROOT))
            + " && python3 -m ESSO synth "
            + shlex.quote(norm_model)
            + " "
            + shlex.quote(norm_synth)
            + " --profile dev --solvers "
            + shlex.quote(solver_list)
            + " --timeout-ms "
            + str(timeout_ms)
            + " --determinism-trials 1 --max-iters 20 --ce-suite-max-size 64"
            + " --portfolio-enum-max-cost 80 --portfolio-enum-max-terms-per-hole 512 --portfolio-enum-max-attempts 300"
            + " --portfolio-mcts-rollouts 200 --portfolio-mcts-max-cost 80 --portfolio-mcts-max-terms-per-hole 128"
            + " --output "
            + shlex.quote(str(run_dir))
        ),
    ]
    cmd_res = _run_cmd(cmd, timeout_s=timeout_s)
    if cmd_res.timeout:
        return {
            "status": "inconclusive",
            "reason": "timeout",
            "signal": None,
            "counterexample": {"model_yaml": norm_model, "synth_json": norm_synth},
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }

    payload = _read_json_dict(run_dir / "result.json") or _extract_json(cmd_res.stdout)
    if not isinstance(payload, dict):
        return {
            "status": "inconclusive",
            "reason": "unparseable_json",
            "signal": None,
            "counterexample": {"run_dir": str(run_dir)},
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    if payload.get("ok") is not True:
        err = payload.get("error")
        err_obj = err if isinstance(err, dict) else {}
        err_msg = str(err_obj.get("message", ""))
        return {
            "status": "inconclusive",
            "reason": "synth_no_candidate",
            "signal": None,
            "counterexample": {"synth_result": payload, "error_message": err_msg},
            "metrics": {
                "model_yaml": norm_model,
                "synth_json": norm_synth,
                "min_mean_ppm": min_ppm_i,
                "samples": sample_n,
                "solvers": solver_list,
                "solver_timeout_ms": timeout_ms,
                "error_message": err_msg,
            },
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }

    filled_holes = payload.get("filled_holes")
    expr, reason = _extract_target_expr(filled_holes, "output_expr")
    if expr is None:
        return {
            "status": "inconclusive",
            "reason": "missing_output_expr",
            "signal": None,
            "counterexample": {"extract_reason": reason, "filled_holes": filled_holes},
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }

    import random

    rng = random.Random(0)
    ratios: list[int] = []
    overdelivery = 0
    attempted = 0
    while len(ratios) < sample_n and attempted < sample_n * 50:
        attempted += 1
        reserve_in = rng.randint(100, 1_000_000)
        reserve_out = rng.randint(100, 1_000_000)
        net_in = rng.randint(1, 100_000)
        if net_in * 10 > reserve_in:
            continue
        exact = int((reserve_out * net_in) // (reserve_in + net_in))
        if exact <= 0:
            continue
        env = {
            "reserve_in": int(reserve_in),
            "reserve_out": int(reserve_out),
            "net_in": int(net_in),
            "dummy": 0,
        }
        approx_raw = _eval_expr_runtime(expr, env)
        approx = max(0, int(_coerce_int(approx_raw)))
        if approx > exact:
            overdelivery += 1
        ratio_ppm = int((approx * 1_000_000) // exact)
        ratios.append(ratio_ppm)

    if not ratios:
        return {
            "status": "inconclusive",
            "reason": "no_valid_samples",
            "signal": None,
            "counterexample": {"attempted": attempted},
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }

    ratios_sorted = sorted(ratios)
    n = len(ratios_sorted)
    mean_ppm = int(sum(ratios_sorted) // n)
    p50_ppm = int(ratios_sorted[n // 2])
    p90_ppm = int(ratios_sorted[min(n - 1, int(n * 0.9))])
    min_ppm_obs = int(ratios_sorted[0])
    max_ppm_obs = int(ratios_sorted[-1])
    signal = bool(mean_ppm >= min_ppm_i and overdelivery == 0)
    counterexample = None
    if not signal:
        counterexample = {
            "mean_ppm": mean_ppm,
            "min_mean_ppm": min_ppm_i,
            "overdelivery_samples": overdelivery,
            "samples_used": n,
        }

    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": counterexample,
        "metrics": {
            "model_yaml": norm_model,
            "synth_json": norm_synth,
            "solvers": solver_list,
            "solver_timeout_ms": timeout_ms,
            "samples_requested": sample_n,
            "samples_used": n,
            "attempted": attempted,
            "min_mean_ppm": min_ppm_i,
            "mean_ratio_ppm": mean_ppm,
            "p50_ratio_ppm": p50_ppm,
            "p90_ratio_ppm": p90_ppm,
            "min_ratio_ppm": min_ppm_obs,
            "max_ratio_ppm": max_ppm_obs,
            "overdelivery_samples": overdelivery,
        },
        "command": cmd,
        "duration_s": cmd_res.duration_s,
        "stdout_tail": cmd_res.stdout[-1200:],
        "stderr_tail": cmd_res.stderr[-1200:],
    }


def _classify_d16_regime(result_payload: dict[str, Any], meta_payload: dict[str, Any]) -> dict[str, Any]:
    portfolio = meta_payload.get("portfolio") if isinstance(meta_payload, dict) else {}
    enum_block = portfolio.get("enum") if isinstance(portfolio, dict) else {}
    enum_metrics = enum_block.get("metrics") if isinstance(enum_block, dict) else {}
    reject_reasons = portfolio.get("reject_reasons") if isinstance(portfolio, dict) else {}
    rr = reject_reasons if isinstance(reject_reasons, dict) else {}
    terms_total = int((enum_metrics or {}).get("terms_generated_total", 0) or 0)

    has_d16 = False
    has_style = False
    for k in rr.keys():
        ks = str(k)
        if "CGS:D16" in ks:
            has_d16 = True
        if "Style:" in ks:
            has_style = True

    ok_flag = bool(result_payload.get("ok") is True)
    label = str(result_payload.get("label", ""))
    err = result_payload.get("error")
    err_obj = err if isinstance(err, dict) else {}
    err_msg = str(err_obj.get("message", ""))

    if has_d16 and terms_total > 0:
        regime = "d16_blocking"
    elif has_d16 and terms_total == 0:
        regime = "d16_pre_enum"
    elif ok_flag:
        regime = "accepted_no_d16"
    elif err_msg.startswith("sygus:"):
        regime = "reject_no_d16"
    else:
        regime = "other"

    return {
        "regime": regime,
        "ok": ok_flag,
        "label": label,
        "error_message": err_msg,
        "terms_generated_total": terms_total,
        "has_d16": has_d16,
        "has_style": has_style,
        "reject_reasons": {str(k): int(v) for k, v in rr.items() if isinstance(v, (int, float))},
    }


def _check_esso_d16_static_expect(mode: str, timeout_s: int, expected: str, synth_json: str) -> dict[str, Any]:
    del timeout_s  # static analysis only
    target = str(expected or "").strip().lower()
    valid_targets = {
        "forced_d16_blocking",
        "division_required_but_d16_safe",
        "div_bypass_possible_nonconst_div",
        "div_bypass_and_d16_safe",
        "no_division",
        "other",
        "any_forced",
        "any_nonforced",
    }
    if target not in valid_targets:
        return {
            "status": "inconclusive",
            "reason": "invalid_expected_static_class",
            "signal": None,
            "counterexample": {"expected": expected, "valid_expected": sorted(valid_targets)},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "invalid expected static class",
        }

    t0 = time.time()
    info, reason = _analyze_synth_d16_static(synth_json)
    if info is None:
        return {
            "status": "inconclusive",
            "reason": reason,
            "signal": None,
            "counterexample": {"synth_json": synth_json},
            "metrics": {},
            "command": [],
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": reason,
        }

    observed = str(info.get("observed_static_class", "other"))
    any_forced = bool(info.get("any_forced", False))
    if target == "any_forced":
        signal = any_forced
    elif target == "any_nonforced":
        signal = not any_forced
    else:
        signal = observed == target
    counterexample = None
    if not signal:
        counterexample = {
            "expected": target,
            "observed": observed,
            "any_forced": any_forced,
            "class_counts": info.get("class_counts", {}),
        }

    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": counterexample,
        "metrics": info,
        "command": [],
        "duration_s": float(time.time() - t0),
        "stdout_tail": "",
        "stderr_tail": "",
    }


def _check_esso_d16_regime_expect(
    mode: str,
    timeout_s: int,
    expected: str,
    model_yaml: str,
    synth_json: str,
    *,
    solvers: str = "cvc5",
    solver_timeout_ms: int = 6000,
) -> dict[str, Any]:
    norm_model = _normalize_kernel_yaml(model_yaml)
    norm_synth = _normalize_synth_json(synth_json)
    if norm_model is None:
        return {
            "status": "inconclusive",
            "reason": "invalid_model_path",
            "signal": None,
            "counterexample": {"model_yaml": model_yaml},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "invalid model path",
        }
    if norm_synth is None:
        return {
            "status": "inconclusive",
            "reason": "invalid_synth_path",
            "signal": None,
            "counterexample": {"synth_json": synth_json},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "invalid synth path",
        }
    solver_list = str(solvers or "").strip()
    if not solver_list or not re.fullmatch(r"[A-Za-z0-9_,.-]+", solver_list):
        return {
            "status": "inconclusive",
            "reason": "invalid_solver_list",
            "signal": None,
            "counterexample": {"model_yaml": norm_model, "synth_json": norm_synth, "solvers": solvers},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "invalid solver list",
        }
    timeout_ms = int(solver_timeout_ms)
    if timeout_ms <= 0:
        return {
            "status": "inconclusive",
            "reason": "invalid_solver_timeout_ms",
            "signal": None,
            "counterexample": {"model_yaml": norm_model, "synth_json": norm_synth, "solver_timeout_ms": timeout_ms},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "invalid solver timeout",
        }
    target = str(expected or "").strip().lower()
    valid_targets = {
        "d16_blocking",
        "d16_pre_enum",
        "accepted_no_d16",
        "reject_no_d16",
        "other",
        "any_reject",
        "any_accept",
    }
    if target not in valid_targets:
        return {
            "status": "inconclusive",
            "reason": "invalid_expected_regime",
            "signal": None,
            "counterexample": {"expected": expected, "valid_expected": sorted(valid_targets)},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "invalid expected regime",
        }

    run_dir = Path(tempfile.mkdtemp(prefix="zenodex_esso_d16_", dir="/tmp"))
    cmd = [
        "bash",
        "-lc",
        (
            "cd "
            + shlex.quote(str(ROOT))
            + " && python3 -m ESSO synth "
            + shlex.quote(norm_model)
            + " "
            + shlex.quote(norm_synth)
            + " --profile dev --solvers "
            + shlex.quote(solver_list)
            + " --timeout-ms "
            + str(timeout_ms)
            + " --determinism-trials 1 --max-iters 20 --ce-suite-max-size 64"
            + " --portfolio-enum-max-cost 80 --portfolio-enum-max-terms-per-hole 512 --portfolio-enum-max-attempts 300"
            + " --portfolio-mcts-rollouts 200 --portfolio-mcts-max-cost 80 --portfolio-mcts-max-terms-per-hole 128"
            + " --output "
            + shlex.quote(str(run_dir))
        ),
    ]
    cmd_res = _run_cmd(cmd, timeout_s=timeout_s)
    if cmd_res.timeout:
        return {
            "status": "inconclusive",
            "reason": "timeout",
            "signal": None,
            "counterexample": {"model_yaml": norm_model, "synth_json": norm_synth},
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }

    result_path = run_dir / "result.json"
    meta_path = run_dir / "artifacts" / "meta.json"
    result_payload = {}
    meta_payload = {}
    if result_path.exists():
        try:
            obj = json.loads(result_path.read_text(encoding="utf-8"))
            if isinstance(obj, dict):
                result_payload = obj
        except Exception:
            result_payload = {}
    if meta_path.exists():
        try:
            obj = json.loads(meta_path.read_text(encoding="utf-8"))
            if isinstance(obj, dict):
                meta_payload = obj
        except Exception:
            meta_payload = {}
    if not result_payload or not meta_payload:
        return {
            "status": "inconclusive",
            "reason": "missing_result_or_meta",
            "signal": None,
            "counterexample": {"run_dir": str(run_dir)},
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }

    regime_info = _classify_d16_regime(result_payload, meta_payload)
    observed = str(regime_info.get("regime", "other"))
    ok_flag = bool(result_payload.get("ok") is True)
    signal = False
    if target == "any_reject":
        signal = not ok_flag
    elif target == "any_accept":
        signal = ok_flag
    else:
        signal = observed == target

    counterexample = None
    if not signal:
        counterexample = {
            "expected": target,
            "observed": observed,
            "regime_info": regime_info,
            "result_error": ((result_payload.get("error") or {}).get("message")),
        }

    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": counterexample,
        "metrics": {
            "model_yaml": norm_model,
            "synth_json": norm_synth,
            "solvers": solver_list,
            "solver_timeout_ms": timeout_ms,
            "expected_regime": target,
            "observed_regime": observed,
            "regime_info": regime_info,
        },
        "command": cmd,
        "duration_s": cmd_res.duration_s,
        "stdout_tail": cmd_res.stdout[-1200:],
        "stderr_tail": cmd_res.stderr[-1200:],
    }


def _classify_esso_synth_regime(payload: dict[str, Any]) -> dict[str, Any]:
    def _extract_sygus_error_signature(run_dir_raw: Any) -> dict[str, Any]:
        run_dir_s = str(run_dir_raw or "").strip()
        if not run_dir_s:
            return {"error_class": "", "signature_line": "", "problem_has_empty_and": False}
        try:
            iter_dir = Path(run_dir_s) / "artifacts" / "sygus" / "iter_001"
        except Exception:
            return {"error_class": "", "signature_line": "", "problem_has_empty_and": False}
        stdout_line = ""
        stderr_line = ""
        problem_text = ""
        try:
            p = iter_dir / "stdout.txt"
            if p.exists():
                stdout_line = next((ln.strip() for ln in p.read_text(encoding="utf-8").splitlines() if ln.strip()), "")
        except Exception:
            stdout_line = ""
        try:
            p = iter_dir / "stderr.txt"
            if p.exists():
                stderr_line = next((ln.strip() for ln in p.read_text(encoding="utf-8").splitlines() if ln.strip()), "")
        except Exception:
            stderr_line = ""
        try:
            p = iter_dir / "sygus_problem.smt2"
            if p.exists():
                problem_text = p.read_text(encoding="utf-8")
        except Exception:
            problem_text = ""

        sig = stdout_line or stderr_line
        low = sig.lower()
        cls = ""
        if "non-linear fact was asserted to arithmetic in a linear logic" in low:
            cls = "nonlinear_in_lia"
        elif "invalid kind 'and'" in low:
            cls = "empty_and"
        elif "error finding token following #" in low:
            cls = "raw_comment_constraint"
        elif "expecting a boolean subexpression" in low:
            if "#" in problem_text:
                cls = "raw_comment_constraint"
            else:
                cls = "non_boolean_subexpr"
        elif "infeasible" in low:
            cls = "infeasible"

        return {
            "error_class": cls,
            "signature_line": sig[:400],
            "problem_has_empty_and": "(and )" in problem_text,
        }

    err = payload.get("error")
    err_obj = err if isinstance(err, dict) else {}
    details = err_obj.get("details")
    details_obj = details if isinstance(details, dict) else {}
    diagnostics = details_obj.get("diagnostics")
    diagnostics_obj = diagnostics if isinstance(diagnostics, dict) else {}

    def _as_int(v: Any) -> int | None:
        try:
            return int(v)
        except Exception:
            return None

    ok_flag = bool(payload.get("ok") is True)
    label = str(payload.get("label", ""))
    error_code = str(err_obj.get("code", ""))
    message = str(err_obj.get("message", ""))
    ce_added = _as_int(details_obj.get("ce_added"))
    iterations = _as_int(details_obj.get("iterations"))
    exit_code = _as_int(payload.get("exit_code"))
    sygus_sig = _extract_sygus_error_signature(payload.get("run_dir"))
    error_class = str(sygus_sig.get("error_class", ""))
    diagnostics_class = str(diagnostics_obj.get("classification", ""))

    if ok_flag:
        regime = "synth_ok"
    elif error_code == "SynthesisFailed" and message == "sygus:duplicate" and ce_added == 0:
        regime = "reject_duplicate_no_ce"
    elif error_code == "SynthesisFailed" and message == "sygus:fail" and ce_added == 0:
        regime = "reject_fail_no_ce"
    elif error_code == "SynthesisFailed" and message == "sygus:error" and ce_added == 0 and iterations == 1:
        regime = "solver_error_pre_ce"
    elif ce_added is not None and ce_added > 0:
        regime = "reject_with_ce"
    elif ce_added == 0:
        regime = "reject_no_ce"
    else:
        regime = "reject_other"
    if regime == "solver_error_pre_ce" and error_class:
        regime = f"solver_error_pre_ce_{error_class}"

    return {
        "regime": regime,
        "ok": ok_flag,
        "label": label,
        "error_code": error_code,
        "message": message,
        "ce_added": ce_added,
        "iterations": iterations,
        "exit_code": exit_code,
        "error_class": error_class,
        "diagnostics_class": diagnostics_class,
        "sygus_signature_line": str(sygus_sig.get("signature_line", "")),
        "problem_has_empty_and": bool(sygus_sig.get("problem_has_empty_and")),
    }


def _check_esso_synth_preflight_expect(
    mode: str,
    timeout_s: int,
    expected: str,
    model_yaml: str,
    synth_json: str,
    *,
    solvers: str = "cvc5",
    solver_timeout_ms: int = 10000,
    max_iters: int = 12,
    ce_suite_max_size: int = 24,
) -> dict[str, Any]:
    norm_model = _normalize_kernel_yaml(model_yaml)
    norm_synth = _normalize_synth_json(synth_json)
    if norm_model is None:
        return {
            "status": "inconclusive",
            "reason": "invalid_model_path",
            "signal": None,
            "counterexample": {"model_yaml": model_yaml},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "invalid model path",
        }
    if norm_synth is None:
        return {
            "status": "inconclusive",
            "reason": "invalid_synth_path",
            "signal": None,
            "counterexample": {"synth_json": synth_json},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "invalid synth path",
        }

    target = str(expected or "").strip().lower()
    valid_targets = {
        "synth_ok",
        "solver_error_pre_ce",
        "solver_error_pre_ce_nonlinear_in_lia",
        "solver_error_pre_ce_empty_and",
        "solver_error_pre_ce_raw_comment_constraint",
        "solver_error_pre_ce_non_boolean_subexpr",
        "solver_error_pre_ce_infeasible",
        "reject_duplicate_no_ce",
        "reject_fail_no_ce",
        "reject_with_ce",
        "reject_no_ce",
        "reject_other",
        "any_reject",
        "any_pass",
    }
    if target not in valid_targets:
        return {
            "status": "inconclusive",
            "reason": "invalid_expected_regime",
            "signal": None,
            "counterexample": {"expected": expected, "valid_expected": sorted(valid_targets)},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "invalid expected regime",
        }

    solver_list = str(solvers or "").strip()
    if not solver_list or not re.fullmatch(r"[A-Za-z0-9_,.-]+", solver_list):
        return {
            "status": "inconclusive",
            "reason": "invalid_solver_list",
            "signal": None,
            "counterexample": {"model_yaml": norm_model, "synth_json": norm_synth, "solvers": solvers},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "invalid solver list",
        }

    timeout_ms = int(solver_timeout_ms)
    if timeout_ms <= 0:
        return {
            "status": "inconclusive",
            "reason": "invalid_solver_timeout_ms",
            "signal": None,
            "counterexample": {"solver_timeout_ms": timeout_ms},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "invalid solver timeout",
        }

    run_dir = Path(tempfile.mkdtemp(prefix="zenodex_esso_preflight_", dir="/tmp"))
    cmd = [
        "bash",
        "-lc",
        (
            "cd "
            + shlex.quote(str(ROOT))
            + " && python3 -m ESSO synth "
            + shlex.quote(norm_model)
            + " "
            + shlex.quote(norm_synth)
            + " --profile dev --solvers "
            + shlex.quote(solver_list)
            + " --timeout-ms "
            + str(timeout_ms)
            + " --determinism-trials 1 --max-iters "
            + str(max(1, int(max_iters)))
            + " --ce-suite-max-size "
            + str(max(1, int(ce_suite_max_size)))
            + " --output "
            + shlex.quote(str(run_dir))
        ),
    ]
    cmd_res = _run_cmd(cmd, timeout_s=timeout_s)
    if cmd_res.timeout:
        return {
            "status": "inconclusive",
            "reason": "timeout",
            "signal": None,
            "counterexample": {"model_yaml": norm_model, "synth_json": norm_synth},
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }

    payload = None
    result_path = run_dir / "result.json"
    if result_path.exists():
        try:
            cand = json.loads(result_path.read_text(encoding="utf-8"))
            if isinstance(cand, dict):
                payload = cand
        except Exception:
            payload = None
    if payload is None:
        payload = _extract_json(cmd_res.stdout)
    if payload is None:
        return {
            "status": "inconclusive",
            "reason": "unparseable_json",
            "signal": None,
            "counterexample": {"model_yaml": norm_model, "synth_json": norm_synth},
            "metrics": {"returncode": cmd_res.returncode},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }

    regime = _classify_esso_synth_regime(payload)
    observed = str(regime.get("regime", ""))
    ok_flag = bool(regime.get("ok"))
    if target == "any_reject":
        signal = not ok_flag
    elif target == "any_pass":
        signal = ok_flag
    else:
        signal = bool(observed == target)

    counterexample = None
    if not signal:
        counterexample = {
            "expected_regime": target,
            "observed_regime": observed,
            "regime_metrics": regime,
            "synth_result": payload,
        }
    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": counterexample,
        "metrics": {
            "model_yaml": norm_model,
            "synth_json": norm_synth,
            "expected_regime": target,
            "observed_regime": observed,
            "regime_metrics": regime,
            "solvers": solver_list,
            "solver_timeout_ms": timeout_ms,
            "max_iters": int(max(1, int(max_iters))),
            "ce_suite_max_size": int(max(1, int(ce_suite_max_size))),
        },
        "command": cmd,
        "duration_s": cmd_res.duration_s,
        "stdout_tail": cmd_res.stdout[-1200:],
        "stderr_tail": cmd_res.stderr[-1200:],
    }


def _check_esso_spec_debug_class(
    mode: str,
    timeout_s: int,
    expected_class: str,
    model_yaml: str,
    synth_json: str,
) -> dict[str, Any]:
    norm_model = _normalize_kernel_yaml(model_yaml)
    norm_synth = _normalize_synth_json(synth_json)
    if norm_model is None:
        return {
            "status": "inconclusive",
            "reason": "invalid_model_path",
            "signal": None,
            "counterexample": {"model_yaml": model_yaml},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "invalid model path",
        }
    if norm_synth is None:
        return {
            "status": "inconclusive",
            "reason": "invalid_synth_path",
            "signal": None,
            "counterexample": {"synth_json": synth_json},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "invalid synth path",
        }

    run_dir = Path(tempfile.mkdtemp(prefix="zenodex_esso_spec_debug_", dir="/tmp"))
    cmd = [
        "bash",
        "-lc",
        (
            "cd "
            + shlex.quote(str(ROOT))
            + " && python3 -m ESSO spec-debug "
            + shlex.quote(norm_model)
            + " "
            + shlex.quote(norm_synth)
            + " --profile dev --output "
            + shlex.quote(str(run_dir))
        ),
    ]
    cmd_res = _run_cmd(cmd, timeout_s=timeout_s)
    if cmd_res.timeout:
        return {
            "status": "inconclusive",
            "reason": "timeout",
            "signal": None,
            "counterexample": {"model_yaml": norm_model, "synth_json": norm_synth},
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    payload = _extract_json(cmd_res.stdout)
    report_path = run_dir / "infeasible_report.json"
    if payload is None and report_path.exists():
        try:
            rep = json.loads(report_path.read_text(encoding="utf-8"))
            payload = {"ok": True, "report": rep}
        except Exception:
            payload = None
    if payload is None:
        return {
            "status": "inconclusive",
            "reason": "unparseable_json",
            "signal": None,
            "counterexample": {"model_yaml": norm_model, "synth_json": norm_synth},
            "metrics": {"returncode": cmd_res.returncode},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    classification = str((payload.get("report") or {}).get("classification", "")).strip().upper()
    target = str(expected_class or "").strip().upper()
    if not target:
        return {
            "status": "inconclusive",
            "reason": "missing_expected_class",
            "signal": None,
            "counterexample": {"expected_class": expected_class},
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    signal = bool(payload.get("ok") is True and classification == target)
    counterexample = None if signal else {"expected_class": target, "actual_class": classification, "report": payload.get("report")}
    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": counterexample,
        "metrics": {
            "model_yaml": norm_model,
            "synth_json": norm_synth,
            "classification": classification,
            "expected_class": target,
            "ok": payload.get("ok"),
        },
        "command": cmd,
        "duration_s": cmd_res.duration_s,
        "stdout_tail": cmd_res.stdout[-1200:],
        "stderr_tail": cmd_res.stderr[-1200:],
    }


def _parse_kv_int_params(spec: str) -> tuple[dict[str, int] | None, str | None]:
    params: dict[str, int] = {}
    raw = str(spec or "").strip()
    if not raw:
        return None, "empty_params"
    for part in raw.split(","):
        part = part.strip()
        if not part:
            continue
        if "=" not in part:
            return None, "missing_equals"
        key, value = part.split("=", 1)
        key = key.strip()
        value = value.strip().replace("_", "")
        if not key:
            return None, "empty_key"
        if not value:
            return None, "empty_value"
        try:
            params[key] = int(value)
        except Exception:
            return None, f"bad_int:{key}"
    if not params:
        return None, "no_params"
    return params, None


def _check_perp_oracle_lp_attack_dynamic(mode: str, timeout_s: int, check_id: str) -> dict[str, Any] | None:
    m = re.match(r"^perp_oracle_lp_attack_(absent|exists)::(.+)$", check_id)
    if not m:
        return None
    kind = str(m.group(1))
    params, err = _parse_kv_int_params(str(m.group(2)))
    if err is not None or params is None:
        return {
            "status": "inconclusive",
            "reason": f"bad_params:{err or 'unknown'}",
            "signal": None,
            "counterexample": {"check_id": check_id},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "bad params",
        }

    required = [
        "rb",
        "rq",
        "fee_bps",
        "pfs",
        "lp_share_bps",
        "max_r",
        "max_pos_abs",
        "max_move_bps",
        "target_profit_quote",
    ]
    missing = [key for key in required if key not in params]
    if missing:
        return {
            "status": "inconclusive",
            "reason": "missing_params",
            "signal": None,
            "counterexample": {"check_id": check_id, "missing": missing},
            "metrics": {"parsed_params": params},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "missing params",
        }

    # Optional: protocol fee rounding (0=floor/v8, 1=ceil/v9)
    pfr = int(params.get("pfr", 0))
    if pfr not in (0, 1):
        return {
            "status": "inconclusive",
            "reason": "bad_params:pfr",
            "signal": None,
            "counterexample": {"check_id": check_id, "pfr": pfr},
            "metrics": {"parsed_params": params},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "bad pfr (expected 0 or 1)",
        }
    pfr_flag = "floor" if pfr == 0 else "ceil"

    cmd = [
        "python3",
        "tools/perp_oracle_manipulation_lp_sweep.py",
        "--reserve-base",
        str(int(params["rb"])),
        "--reserve-quote",
        str(int(params["rq"])),
        "--fee-bps",
        str(int(params["fee_bps"])),
        "--lp-share-bps",
        str(int(params["lp_share_bps"])),
        "--max-r",
        str(int(params["max_r"])),
        "--max-pos-abs",
        str(int(params["max_pos_abs"])),
        "--max-move-bps",
        str(int(params["max_move_bps"])),
        "--target-profit-quote",
        str(int(params["target_profit_quote"])),
        "--protocol-fee-rounding",
        str(pfr_flag),
        "--protocol-fee-share-bps",
        str(int(params["pfs"])),
    ]
    cmd_res = _run_cmd(cmd, timeout_s=timeout_s)
    if cmd_res.timeout:
        return {
            "status": "inconclusive",
            "reason": "timeout",
            "signal": None,
            "counterexample": None,
            "metrics": {"params": params},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    payload = _extract_json(cmd_res.stdout)
    if not cmd_res.ok or payload is None:
        return {
            "status": "inconclusive",
            "reason": "command_error_or_unparseable_json",
            "signal": None,
            "counterexample": None,
            "metrics": {"params": params},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    rows = payload.get("rows")
    if not isinstance(rows, list) or not rows:
        return {
            "status": "inconclusive",
            "reason": "missing_rows",
            "signal": None,
            "counterexample": None,
            "metrics": {"params": params},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }

    pfs = int(params["pfs"])
    attack_found: bool | None = None
    witness: Any = None
    for row in rows:
        try:
            if int(row.get("protocol_fee_share_bps", -1)) != pfs:
                continue
            attack_found = bool(row.get("attack_found", False))
            witness = row.get("witness")
            break
        except Exception:
            continue
    if attack_found is None:
        return {
            "status": "inconclusive",
            "reason": "missing_row_for_pfs",
            "signal": None,
            "counterexample": {"pfs": pfs, "rows": rows[:3]},
            "metrics": {"params": params},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }

    if kind == "absent":
        signal = not attack_found
        counterexample = witness if attack_found else None
    else:
        signal = bool(attack_found)
        counterexample = witness if attack_found else None

    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": counterexample,
        "metrics": {"params": params, "attack_found": bool(attack_found)},
        "command": cmd,
        "duration_s": cmd_res.duration_s,
        "stdout_tail": cmd_res.stdout[-1200:],
        "stderr_tail": cmd_res.stderr[-1200:],
    }


def _check_split_routing_case_dynamic(mode: str, timeout_s: int, check_id: str) -> dict[str, Any] | None:
    """
    Deterministic split-routing oracle check on a *single* concrete case.

    Formats:
    - split_routing_case_optimal::<profile>::x0=..,y0=..,fee0=..,x1=..,y1=..,fee1=..,amount_in=..,window=..
      signal := (heuristic matches brute-force output AND canonical tie-break a)
    - split_routing_case_gap_exists::<profile>::... ,min_gap=1
      signal := (brute_out - heur_out) >= min_gap
    """
    m = re.match(r"^split_routing_case_(optimal|gap_exists)::([A-Za-z0-9_]+)::(.+)$", check_id)
    if not m:
        return None
    kind = str(m.group(1))
    profile = str(m.group(2))
    params, err = _parse_kv_int_params(str(m.group(3)))
    if err is not None or params is None:
        return {
            "status": "inconclusive",
            "reason": f"bad_params:{err or 'unknown'}",
            "signal": None,
            "counterexample": {"check_id": check_id},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "bad params",
        }

    required = ["x0", "y0", "fee0", "x1", "y1", "fee1", "amount_in", "window"]
    missing = [k for k in required if k not in params]
    if missing:
        return {
            "status": "inconclusive",
            "reason": "missing_params",
            "signal": None,
            "counterexample": {"check_id": check_id, "missing": missing},
            "metrics": {"parsed_params": params, "profile": profile},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "missing params",
        }

    t0 = time.time()
    cmd = ["internal_python_eval", "split_routing_case", kind, profile]
    try:
        import sys  # pylint: disable=import-outside-toplevel

        if str(ROOT) not in sys.path:
            sys.path.insert(0, str(ROOT))
        from src.core.split_routing import (  # pylint: disable=import-outside-toplevel
            PoolXY,
            brute_force_best_split_two_pools_exact_in,
            best_split_two_pools_exact_in,
            resolve_two_pool_split_search_params,
        )
    except Exception as exc:
        return {
            "status": "inconclusive",
            "reason": "import_error",
            "signal": None,
            "counterexample": {"error": str(exc)},
            "metrics": {"profile": profile, "params": params},
            "command": cmd,
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": str(exc)[-1200:],
        }

    p0 = PoolXY(x=int(params["x0"]), y=int(params["y0"]), fee_bps=int(params["fee0"]))
    p1 = PoolXY(x=int(params["x1"]), y=int(params["y1"]), fee_bps=int(params["fee1"]))
    amount_in = int(params["amount_in"])
    window = int(params["window"])

    try:
        brute_out, brute_a = brute_force_best_split_two_pools_exact_in(p0, p1, amount_in)
        resolved_window = int(window)
        resolved_profile = str(profile)
        if resolved_profile.strip().lower().startswith("adaptive_"):
            resolved_window, resolved_profile = resolve_two_pool_split_search_params(
                p0,
                p1,
                amount_in,
                search_profile=str(profile),
                window=int(window),
            )
        heur_out, heur_a = best_split_two_pools_exact_in(
            p0,
            p1,
            amount_in,
            window=int(resolved_window),
            search_profile=str(resolved_profile),
        )
    except Exception as exc:
        return {
            "status": "inconclusive",
            "reason": "invalid_case",
            "signal": None,
            "counterexample": {"error": str(exc), "profile": profile, "params": params},
            "metrics": {"profile": profile, "params": params},
            "command": cmd,
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": str(exc)[-1200:],
        }

    gap = int(brute_out) - int(heur_out)

    if kind == "optimal":
        signal = bool(int(heur_out) == int(brute_out) and int(heur_a) == int(brute_a))
        counterexample = None
        if not signal:
            counterexample = {
                "profile": profile,
                "params": params,
                "oracle": {"out": int(brute_out), "a": int(brute_a)},
                "heuristic": {"out": int(heur_out), "a": int(heur_a)},
                "gap": gap,
                "resolved": {"window": int(resolved_window), "profile": str(resolved_profile)},
            }
    else:
        min_gap = int(params.get("min_gap", 1))
        if min_gap <= 0:
            return {
                "status": "inconclusive",
                "reason": "bad_params:min_gap",
                "signal": None,
                "counterexample": {"check_id": check_id, "min_gap": min_gap},
                "metrics": {"profile": profile, "params": params},
                "command": cmd,
                "duration_s": float(time.time() - t0),
                "stdout_tail": "",
                "stderr_tail": "min_gap must be positive",
            }
        signal = bool(gap >= min_gap)
        counterexample = None
        if signal:
            counterexample = {
                "profile": profile,
                "params": params,
                "oracle": {"out": int(brute_out), "a": int(brute_a)},
                "heuristic": {"out": int(heur_out), "a": int(heur_a)},
                "gap": gap,
                "resolved": {"window": int(resolved_window), "profile": str(resolved_profile)},
            }

    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": counterexample,
        "metrics": {
            "kind": kind,
            "profile": profile,
            "resolved_profile": str(resolved_profile),
            "resolved_window": int(resolved_window),
            "params": params,
            "oracle_out": int(brute_out),
            "oracle_a": int(brute_a),
            "heur_out": int(heur_out),
            "heur_a": int(heur_a),
            "gap": gap,
        },
        "command": cmd,
        "duration_s": float(time.time() - t0),
        "stdout_tail": "",
        "stderr_tail": "",
    }


def _check_split_routing_tradeoff_dynamic(mode: str, timeout_s: int, check_id: str) -> dict[str, Any] | None:
    """
    Deterministic tradeoff check for 2-pool CPMM split search policies.

    Format:
    - split_routing_tradeoff::<policy>::seed=..,n=..,match_bp=..,avg_calls_max=..

    policy options:
    - baseline_w64
    - dense24_w64
    - dense24_w96
    - dense32_w64
    - dense32_w96
    - adaptive_v1
    - adaptive_v2
    - adaptive_v3
    - adaptive_v4
    - adaptive_v5
    - adaptive_v6
    - adaptive_v7
    - baseline_canon16_w64

    Interpretation:
    - match_min = match_bp / 10_000
    signal := (oracle_match_rate >= match_min) AND (avg_policy_calls <= avg_calls_max)

    Optional distribution parameters (all integers, inclusive ranges):
    - x_min, x_max: reserve_in range per pool (default 20..400)
    - y_min, y_max: reserve_out range per pool (default 20..400)
    - fee_min, fee_max: fee_bps range per pool (default 0..100)
    - D_min, D_max: amount_in range (default 5000..9000; intended to exceed brute_force_max=4096)
    """
    m = re.match(r"^split_routing_tradeoff::([A-Za-z0-9_]+)::(.+)$", check_id)
    if not m:
        return None
    policy = str(m.group(1)).strip()
    params, err = _parse_kv_int_params(str(m.group(2)))
    if err is not None or params is None:
        return {
            "status": "inconclusive",
            "reason": f"bad_params:{err or 'unknown'}",
            "signal": None,
            "counterexample": {"check_id": check_id},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "bad params",
        }

    required = ["seed", "n", "match_bp", "avg_calls_max"]
    missing = [k for k in required if k not in params]
    if missing:
        return {
            "status": "inconclusive",
            "reason": "missing_params",
            "signal": None,
            "counterexample": {"check_id": check_id, "missing": missing},
            "metrics": {"parsed_params": params, "policy": policy},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "missing params",
        }

    t0 = time.time()
    cmd = ["internal_python_eval", "split_routing_tradeoff", policy]
    try:
        import random  # pylint: disable=import-outside-toplevel
        import sys  # pylint: disable=import-outside-toplevel

        if str(ROOT) not in sys.path:
            sys.path.insert(0, str(ROOT))
        import src.core.split_routing as sr  # pylint: disable=import-outside-toplevel
    except Exception as exc:
        return {
            "status": "inconclusive",
            "reason": "import_error",
            "signal": None,
            "counterexample": {"error": str(exc)},
            "metrics": {"policy": policy, "params": params},
            "command": cmd,
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": str(exc)[-1200:],
        }

    seed = int(params["seed"])
    n = int(params["n"])
    if n <= 0:
        return {
            "status": "inconclusive",
            "reason": "bad_params:n",
            "signal": None,
            "counterexample": {"check_id": check_id, "n": n},
            "metrics": {"policy": policy, "params": params},
            "command": cmd,
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": "n must be positive",
        }

    match_min = float(int(params["match_bp"])) / 10_000.0
    avg_calls_max = int(params["avg_calls_max"])
    if avg_calls_max <= 0:
        return {
            "status": "inconclusive",
            "reason": "bad_params:avg_calls_max",
            "signal": None,
            "counterexample": {"check_id": check_id, "avg_calls_max": avg_calls_max},
            "metrics": {"policy": policy, "params": params},
            "command": cmd,
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": "avg_calls_max must be positive",
        }

    def _parse_policy(p: str) -> tuple[str, int] | None:
        low = str(p).strip().lower()
        if low in {"adaptive_v1", "adaptive_v2", "adaptive_v3", "adaptive_v4", "adaptive_v5", "adaptive_v6", "adaptive_v7"}:
            return (low, 96)
        m2 = re.match(r"^([a-z0-9_]+)_w(\d+)$", low)
        if not m2:
            return None
        prof = str(m2.group(1))
        win = int(m2.group(2))
        if prof not in {"baseline", "dense24", "dense32", "baseline_canon16"}:
            return None
        return (prof, win)

    parsed = _parse_policy(policy)
    if parsed is None:
        return {
            "status": "inconclusive",
            "reason": "bad_policy",
            "signal": None,
            "counterexample": {"policy": policy},
            "metrics": {"policy": policy, "params": params},
            "command": cmd,
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": "unsupported policy",
        }

    # Distribution parameters (optional; keep defaults stable for replay).
    x_min = int(params.get("x_min", 20))
    x_max = int(params.get("x_max", 400))
    y_min = int(params.get("y_min", 20))
    y_max = int(params.get("y_max", 400))
    fee_min = int(params.get("fee_min", 0))
    fee_max = int(params.get("fee_max", 100))
    D_min = int(params.get("D_min", 5000))
    D_max = int(params.get("D_max", 9000))

    if x_min <= 0 or y_min <= 0:
        return {
            "status": "inconclusive",
            "reason": "bad_params:reserve_min",
            "signal": None,
            "counterexample": {"check_id": check_id, "x_min": x_min, "y_min": y_min},
            "metrics": {"policy": policy, "params": params},
            "command": cmd,
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": "reserve mins must be positive",
        }
    if x_max < x_min or y_max < y_min:
        return {
            "status": "inconclusive",
            "reason": "bad_params:reserve_range",
            "signal": None,
            "counterexample": {"check_id": check_id, "x_min": x_min, "x_max": x_max, "y_min": y_min, "y_max": y_max},
            "metrics": {"policy": policy, "params": params},
            "command": cmd,
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": "reserve ranges must be non-decreasing",
        }
    if fee_min < 0 or fee_max < fee_min or fee_max > 10_000:
        return {
            "status": "inconclusive",
            "reason": "bad_params:fee_range",
            "signal": None,
            "counterexample": {"check_id": check_id, "fee_min": fee_min, "fee_max": fee_max},
            "metrics": {"policy": policy, "params": params},
            "command": cmd,
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": "fee range invalid",
        }
    if D_min <= 0 or D_max < D_min:
        return {
            "status": "inconclusive",
            "reason": "bad_params:D_range",
            "signal": None,
            "counterexample": {"check_id": check_id, "D_min": D_min, "D_max": D_max},
            "metrics": {"policy": policy, "params": params},
            "command": cmd,
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": "amount_in range invalid",
        }
    # This check is intended to exercise the heuristic path (brute_force_max=4096).
    if D_min <= 4096:
        return {
            "status": "inconclusive",
            "reason": "bad_params:D_min",
            "signal": None,
            "counterexample": {"check_id": check_id, "D_min": D_min},
            "metrics": {"policy": policy, "params": params},
            "command": cmd,
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": "D_min must exceed brute_force_max=4096 to measure heuristic tradeoffs",
        }

    random.seed(int(seed))

    # Call counter (approx compute proxy).
    orig_exact_out = sr.exact_out_for_pool_exact_in
    call_counter = {"n": 0}

    def _counting_exact_out(pool: sr.PoolXY, amount_in: int) -> int:  # type: ignore[name-defined]
        call_counter["n"] = int(call_counter["n"]) + 1
        return orig_exact_out(pool, amount_in)

    sr.exact_out_for_pool_exact_in = _counting_exact_out  # type: ignore[assignment]
    try:
        cases: list[dict[str, int]] = []
        attempts = 0
        # Keep deterministic and bounded.
        max_attempts = max(200, 80 * int(n))
        while len(cases) < int(n) and attempts < max_attempts:
            attempts += 1
            x0 = random.randint(int(x_min), int(x_max))
            y0 = random.randint(int(y_min), int(y_max))
            x1 = random.randint(int(x_min), int(x_max))
            y1 = random.randint(int(y_min), int(y_max))
            fee0 = random.randint(int(fee_min), int(fee_max))
            fee1 = random.randint(int(fee_min), int(fee_max))
            # Intended to exceed brute_force_max=4096 so we measure real policy tradeoffs.
            D = random.randint(int(D_min), int(D_max))
            row = {"x0": x0, "y0": y0, "fee0": fee0, "x1": x1, "y1": y1, "fee1": fee1, "amount_in": D}

            p0 = sr.PoolXY(x=int(x0), y=int(y0), fee_bps=int(fee0))
            p1 = sr.PoolXY(x=int(x1), y=int(y1), fee_bps=int(fee1))
            try:
                sr.brute_force_best_split_two_pools_exact_in(p0, p1, int(D))
            except Exception:
                continue
            cases.append(row)

        if len(cases) < int(n):
            return {
                "status": "inconclusive",
                "reason": "insufficient_feasible_cases",
                "signal": None,
                "counterexample": {"built": len(cases), "target": int(n), "attempts": attempts},
                "metrics": {"policy": policy, "params": params},
                "command": cmd,
                "duration_s": float(time.time() - t0),
                "stdout_tail": "",
                "stderr_tail": "could not generate enough feasible cases",
            }

        match_count = 0
        out_match_count = 0
        tie_mismatch_count = 0
        gap_mismatch_count = 0
        policy_calls_total = 0
        worst_calls = -1
        worst_calls_case: dict[str, Any] | None = None
        worst_gap = 0
        worst_case: dict[str, Any] | None = None
        worst_tie_delta = -1
        worst_tie_case: dict[str, Any] | None = None

        for c in cases:
            p0 = sr.PoolXY(x=int(c["x0"]), y=int(c["y0"]), fee_bps=int(c["fee0"]))
            p1 = sr.PoolXY(x=int(c["x1"]), y=int(c["y1"]), fee_bps=int(c["fee1"]))
            D = int(c["amount_in"])

            # Oracle
            brute_out, brute_a = sr.brute_force_best_split_two_pools_exact_in(p0, p1, int(D))

            # Policy selection
            prof, win = parsed
            resolved_prof = prof
            resolved_win = int(win)
            if str(prof).strip().lower().startswith("adaptive_"):
                resolved_win, resolved_prof = sr.resolve_two_pool_split_search_params(
                    p0,
                    p1,
                    D,
                    search_profile=str(prof),
                    window=int(win),
                )

            call_counter["n"] = 0
            heur_out, heur_a = sr.best_split_two_pools_exact_in(
                p0,
                p1,
                int(D),
                window=int(resolved_win),
                search_profile=str(resolved_prof),
            )
            policy_calls = int(call_counter["n"])
            policy_calls_total += policy_calls

            gap = int(brute_out) - int(heur_out)
            out_match = bool(gap == 0)
            tie_match = bool(int(heur_a) == int(brute_a))
            if out_match:
                out_match_count += 1
                if not tie_match:
                    tie_mismatch_count += 1
            else:
                gap_mismatch_count += 1

            if out_match and tie_match:
                match_count += 1

            # Capture the worst compute case (highest policy_calls) so call-budget failures have a witness.
            if int(policy_calls) > int(worst_calls):
                worst_calls = int(policy_calls)
                worst_calls_case = {
                    "case": dict(c),
                    "oracle": {"out": int(brute_out), "a": int(brute_a)},
                    "heuristic": {"out": int(heur_out), "a": int(heur_a)},
                    "resolved": {"window": int(resolved_win), "profile": str(resolved_prof)},
                    "policy_calls": int(policy_calls),
                    "gap": int(gap),
                }

            # Capture the worst output gap (primary) OR, when gaps are all zero, capture the worst tie-break mismatch.
            if gap > worst_gap:
                worst_gap = int(gap)
                worst_case = {
                    "case": dict(c),
                    "oracle": {"out": int(brute_out), "a": int(brute_a)},
                    "heuristic": {"out": int(heur_out), "a": int(heur_a)},
                    "resolved": {"window": int(resolved_win), "profile": str(resolved_prof)},
                    "policy_calls": int(policy_calls),
                    "gap": int(gap),
                }

            if out_match and not tie_match:
                tie_delta = abs(int(heur_a) - int(brute_a))
                if tie_delta > int(worst_tie_delta):
                    worst_tie_delta = int(tie_delta)
                    worst_tie_case = {
                        "case": dict(c),
                        "oracle": {"out": int(brute_out), "a": int(brute_a)},
                        "heuristic": {"out": int(heur_out), "a": int(heur_a)},
                        "resolved": {"window": int(resolved_win), "profile": str(resolved_prof)},
                        "policy_calls": int(policy_calls),
                        "gap": int(gap),
                        "tie_delta": int(tie_delta),
                    }

        match_rate = float(match_count) / float(n)
        avg_calls = float(policy_calls_total) / float(n)

        signal = bool(match_rate >= match_min and avg_calls <= float(avg_calls_max))
        if signal:
            counterexample = None
        else:
            # Prefer an output-gap witness. If there is no output gap, fall back to a tie-break mismatch witness.
            counterexample = {
                "worst_case": worst_case if worst_case is not None else worst_tie_case,
                "worst_gap": int(worst_gap),
                "worst_tie_case": worst_tie_case,
                "worst_tie_delta": int(worst_tie_delta),
                "worst_calls": int(worst_calls),
                "worst_calls_case": worst_calls_case,
            }
        return {
            "status": _mode_status(mode=mode, signal=signal),
            "reason": "ok",
            "signal": signal,
            "counterexample": counterexample,
            "metrics": {
                "policy": str(policy),
                "parsed_policy": {"profile": str(parsed[0]), "window": int(parsed[1])},
                "params": params,
                "oracle_match_rate": float(match_rate),
                "oracle_match_count": int(match_count),
                "oracle_out_match_count": int(out_match_count),
                "tie_mismatch_count": int(tie_mismatch_count),
                "gap_mismatch_count": int(gap_mismatch_count),
                "n": int(n),
                "avg_policy_calls": float(avg_calls),
                "policy_calls_total": int(policy_calls_total),
                "worst_calls": int(worst_calls),
                "worst_gap": int(worst_gap),
            },
            "command": cmd,
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": "",
        }
    finally:
        sr.exact_out_for_pool_exact_in = orig_exact_out  # type: ignore[assignment]


def _check_exact_out_split_tradeoff_dynamic(mode: str, timeout_s: int, check_id: str) -> dict[str, Any] | None:
    """
    Deterministic tradeoff check for 2-pool exact-out splitting policies.

    Format:
    - exact_out_split_tradeoff::<policy>::seed=..,n=..,match_bp=..,avg_calls_max=..,out_min=..,out_max=..

    policy options:
    - default
    - w32 / w64 / w96 / w128 / w192

    Interpretation:
    - match_min = match_bp / 10_000
    signal := (oracle_match_rate >= match_min) AND (avg_policy_calls <= avg_calls_max)
              AND (worst_calls <= worst_calls_max, if provided)

    Optional distribution parameters (all integers, inclusive ranges):
    - x_min, x_max: reserve_in range per pool (default 100..4000)
    - y_min, y_max: reserve_out range per pool (default 100..4000)
    - fee_min, fee_max: fee_bps range per pool (default 0..100)
    - bf_max: brute_force_max used by heuristic (default 512)
    - worst_calls_max: optional per-case call SLA (hard cap)

    Note: This check is intended to exercise the heuristic path, so it requires `out_min > bf_max`.
    """
    m = re.match(r"^exact_out_split_tradeoff::([A-Za-z0-9_]+)::(.+)$", check_id)
    if not m:
        return None
    policy = str(m.group(1)).strip()
    params, err = _parse_kv_int_params(str(m.group(2)))
    if err is not None or params is None:
        return {
            "status": "inconclusive",
            "reason": f"bad_params:{err or 'unknown'}",
            "signal": None,
            "counterexample": {"check_id": check_id},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "bad params",
        }

    required = ["seed", "n", "match_bp", "avg_calls_max", "out_min", "out_max"]
    missing = [k for k in required if k not in params]
    if missing:
        return {
            "status": "inconclusive",
            "reason": "missing_params",
            "signal": None,
            "counterexample": {"check_id": check_id, "missing": missing},
            "metrics": {"parsed_params": params, "policy": policy},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "missing params",
        }

    t0 = time.time()
    cmd = ["internal_python_eval", "exact_out_split_tradeoff", policy]
    try:
        import random  # pylint: disable=import-outside-toplevel
        import sys  # pylint: disable=import-outside-toplevel

        if str(ROOT) not in sys.path:
            sys.path.insert(0, str(ROOT))
        import src.core.split_routing_dispatch as srd  # pylint: disable=import-outside-toplevel
        from src.state.pools import PoolState, PoolStatus  # pylint: disable=import-outside-toplevel
    except Exception as exc:
        return {
            "status": "inconclusive",
            "reason": "import_error",
            "signal": None,
            "counterexample": {"error": str(exc)},
            "metrics": {"policy": policy, "params": params},
            "command": cmd,
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": str(exc)[-1200:],
        }

    seed = int(params["seed"])
    n = int(params["n"])
    if n <= 0:
        return {
            "status": "inconclusive",
            "reason": "bad_params:n",
            "signal": None,
            "counterexample": {"check_id": check_id, "n": n},
            "metrics": {"policy": policy, "params": params},
            "command": cmd,
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": "n must be positive",
        }

    match_min = float(int(params["match_bp"])) / 10_000.0
    avg_calls_max = int(params["avg_calls_max"])
    if avg_calls_max <= 0:
        return {
            "status": "inconclusive",
            "reason": "bad_params:avg_calls_max",
            "signal": None,
            "counterexample": {"check_id": check_id, "avg_calls_max": avg_calls_max},
            "metrics": {"policy": policy, "params": params},
            "command": cmd,
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": "avg_calls_max must be positive",
        }

    worst_calls_max = params.get("worst_calls_max")
    if worst_calls_max is not None:
        worst_calls_max = int(worst_calls_max)
        if worst_calls_max <= 0:
            return {
                "status": "inconclusive",
                "reason": "bad_params:worst_calls_max",
                "signal": None,
                "counterexample": {"check_id": check_id, "worst_calls_max": worst_calls_max},
                "metrics": {"policy": policy, "params": params},
                "command": cmd,
                "duration_s": float(time.time() - t0),
                "stdout_tail": "",
                "stderr_tail": "worst_calls_max must be positive",
            }

    out_min = int(params["out_min"])
    out_max = int(params["out_max"])
    if out_min <= 0 or out_max < out_min:
        return {
            "status": "inconclusive",
            "reason": "bad_params:out_range",
            "signal": None,
            "counterexample": {"check_id": check_id, "out_min": out_min, "out_max": out_max},
            "metrics": {"policy": policy, "params": params},
            "command": cmd,
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": "amount_out range invalid",
        }

    bf_max = int(params.get("bf_max", 512))
    if bf_max < 0:
        return {
            "status": "inconclusive",
            "reason": "bad_params:bf_max",
            "signal": None,
            "counterexample": {"check_id": check_id, "bf_max": bf_max},
            "metrics": {"policy": policy, "params": params},
            "command": cmd,
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": "bf_max must be non-negative",
        }
    if out_min <= bf_max:
        return {
            "status": "inconclusive",
            "reason": "bad_params:out_min",
            "signal": None,
            "counterexample": {"check_id": check_id, "out_min": out_min, "bf_max": bf_max},
            "metrics": {"policy": policy, "params": params},
            "command": cmd,
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": "out_min must exceed bf_max to measure heuristic tradeoffs",
        }

    def _parse_window(p: str) -> int | None:
        low = str(p).strip().lower()
        if low == "default":
            return 64
        m2 = re.match(r"^w(\d+)$", low)
        if not m2:
            return None
        return int(m2.group(1))

    window = _parse_window(policy)
    if window is None:
        return {
            "status": "inconclusive",
            "reason": "bad_policy",
            "signal": None,
            "counterexample": {"check_id": check_id, "policy": policy},
            "metrics": {"policy": policy, "params": params},
            "command": cmd,
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": "unsupported policy",
        }

    # Optional distribution parameters.
    x_min = int(params.get("x_min", 100))
    x_max = int(params.get("x_max", 4000))
    y_min = int(params.get("y_min", 100))
    y_max = int(params.get("y_max", 4000))
    fee_min = int(params.get("fee_min", 0))
    fee_max = int(params.get("fee_max", 100))
    if x_min <= 0 or x_max < x_min or y_min <= 0 or y_max < y_min:
        return {
            "status": "inconclusive",
            "reason": "bad_params:reserve_range",
            "signal": None,
            "counterexample": {"check_id": check_id, "x_min": x_min, "x_max": x_max, "y_min": y_min, "y_max": y_max},
            "metrics": {"policy": policy, "params": params},
            "command": cmd,
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": "reserve range invalid",
        }
    if fee_min < 0 or fee_max < fee_min or fee_max > 10_000:
        return {
            "status": "inconclusive",
            "reason": "bad_params:fee_range",
            "signal": None,
            "counterexample": {"check_id": check_id, "fee_min": fee_min, "fee_max": fee_max},
            "metrics": {"policy": policy, "params": params},
            "command": cmd,
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": "fee range invalid",
        }

    random.seed(int(seed))

    orig_quote = srd._quote_exact_out
    call_counter = {"n": 0}

    def _counting_quote(pool: PoolState, *, asset_in: AssetId, asset_out: AssetId, amount_out: Amount) -> int:  # type: ignore[name-defined]
        call_counter["n"] = int(call_counter["n"]) + 1
        return orig_quote(pool, asset_in=asset_in, asset_out=asset_out, amount_out=amount_out)

    def oracle_total_in(p0: PoolState, p1: PoolState, *, amount_out_total: int) -> tuple[int, int]:
        # Brute-force oracle: scan all q0 in the feasible range, choose min input; tie-break by smaller q0.
        Q = int(amount_out_total)
        r0 = srd._reserves_for(p0, asset_in="A", asset_out="B")
        r1 = srd._reserves_for(p1, asset_in="A", asset_out="B")
        assert r0 is not None and r1 is not None
        _rin0, rout0 = r0
        _rin1, rout1 = r1
        max0 = max(0, int(rout0) - 1)
        max1 = max(0, int(rout1) - 1)
        lo = max(0, int(Q) - int(max1))
        hi = min(int(Q), int(max0))
        best_in: int | None = None
        best_q0 = int(lo)
        for q0 in range(int(lo), int(hi) + 1):
            q1 = int(Q) - int(q0)
            try:
                in0 = orig_quote(p0, asset_in="A", asset_out="B", amount_out=int(q0)) if q0 > 0 else 0
                in1 = orig_quote(p1, asset_in="A", asset_out="B", amount_out=int(q1)) if q1 > 0 else 0
            except Exception:
                continue
            tot = int(in0 + in1)
            if best_in is None or tot < best_in or (tot == best_in and q0 < best_q0):
                best_in = int(tot)
                best_q0 = int(q0)
        if best_in is None:
            raise ValueError("no feasible split")
        return int(best_in), int(best_q0)

    # Patch quote function for compute-counting within the heuristic solver only.
    srd._quote_exact_out = _counting_quote  # type: ignore[assignment]
    try:
        cases: list[dict[str, int]] = []
        attempts = 0
        max_attempts = max(200, 80 * int(n))
        while len(cases) < int(n) and attempts < max_attempts:
            attempts += 1
            x0 = random.randint(int(x_min), int(x_max))
            y0 = random.randint(int(y_min), int(y_max))
            x1 = random.randint(int(x_min), int(x_max))
            y1 = random.randint(int(y_min), int(y_max))
            fee0 = random.randint(int(fee_min), int(fee_max))
            fee1 = random.randint(int(fee_min), int(fee_max))

            # Ensure output doesn't trivially exceed the aggregate reserve_out budget.
            out_cap = int(y0 + y1 - 2)
            if out_cap < out_min:
                continue
            Q = random.randint(int(out_min), min(int(out_max), int(out_cap)))

            # Router works with PoolState objects; keep pool_ids deterministic.
            p0 = PoolState(
                pool_id="p0",
                asset0="A",
                asset1="B",
                reserve0=int(x0),
                reserve1=int(y0),
                fee_bps=int(fee0),
                lp_supply=1,
                status=PoolStatus.ACTIVE,
                created_at=0,
            )
            p1 = PoolState(
                pool_id="p1",
                asset0="A",
                asset1="B",
                reserve0=int(x1),
                reserve1=int(y1),
                fee_bps=int(fee1),
                lp_supply=1,
                status=PoolStatus.ACTIVE,
                created_at=0,
            )

            try:
                _oracle_in, _oracle_q0 = oracle_total_in(p0, p1, amount_out_total=int(Q))
            except Exception:
                continue
            cases.append({"x0": x0, "y0": y0, "fee0": fee0, "x1": x1, "y1": y1, "fee1": fee1, "amount_out": Q})

        if len(cases) < int(n):
            return {
                "status": "inconclusive",
                "reason": "insufficient_feasible_cases",
                "signal": None,
                "counterexample": {"built": len(cases), "target": int(n), "attempts": attempts},
                "metrics": {"policy": policy, "params": params},
                "command": cmd,
                "duration_s": float(time.time() - t0),
                "stdout_tail": "",
                "stderr_tail": "could not generate enough feasible cases",
            }

        match_count = 0
        in_match_count = 0
        tie_mismatch_count = 0
        gap_mismatch_count = 0
        policy_calls_total = 0
        worst_calls = -1
        worst_calls_case: dict[str, Any] | None = None
        worst_gap = 0
        worst_case: dict[str, Any] | None = None
        worst_tie_delta = -1
        worst_tie_case: dict[str, Any] | None = None

        for c in cases:
            p0 = PoolState(
                pool_id="p0",
                asset0="A",
                asset1="B",
                reserve0=int(c["x0"]),
                reserve1=int(c["y0"]),
                fee_bps=int(c["fee0"]),
                lp_supply=1,
                status=PoolStatus.ACTIVE,
                created_at=0,
            )
            p1 = PoolState(
                pool_id="p1",
                asset0="A",
                asset1="B",
                reserve0=int(c["x1"]),
                reserve1=int(c["y1"]),
                fee_bps=int(c["fee1"]),
                lp_supply=1,
                status=PoolStatus.ACTIVE,
                created_at=0,
            )
            Q = int(c["amount_out"])

            # Oracle
            oracle_in, oracle_q0 = oracle_total_in(p0, p1, amount_out_total=int(Q))

            call_counter["n"] = 0
            heur = srd.best_split_two_pools_exact_out_for_pools(
                p0,
                p1,
                asset_in="A",
                asset_out="B",
                amount_out_total=int(Q),
                window=int(window),
                brute_force_max=int(bf_max),
            )
            policy_calls = int(call_counter["n"])
            policy_calls_total += int(policy_calls)

            heur_in = int(heur.amount_in_total)
            heur_q0 = int(heur.amount_out_0)

            gap = int(heur_in) - int(oracle_in)
            in_match = bool(gap == 0)
            tie_match = bool(int(heur_q0) == int(oracle_q0))
            if in_match:
                in_match_count += 1
                if not tie_match:
                    tie_mismatch_count += 1
            else:
                gap_mismatch_count += 1

            if in_match and tie_match:
                match_count += 1

            if int(policy_calls) > int(worst_calls):
                worst_calls = int(policy_calls)
                worst_calls_case = {
                    "case": dict(c),
                    "oracle": {"in": int(oracle_in), "q0": int(oracle_q0)},
                    "heuristic": {"in": int(heur_in), "q0": int(heur_q0)},
                    "window": int(window),
                    "bf_max": int(bf_max),
                    "policy_calls": int(policy_calls),
                    "gap": int(gap),
                }

            if gap > worst_gap:
                worst_gap = int(gap)
                worst_case = {
                    "case": dict(c),
                    "oracle": {"in": int(oracle_in), "q0": int(oracle_q0)},
                    "heuristic": {"in": int(heur_in), "q0": int(heur_q0)},
                    "window": int(window),
                    "bf_max": int(bf_max),
                    "policy_calls": int(policy_calls),
                    "gap": int(gap),
                }

            if in_match and not tie_match:
                tie_delta = abs(int(heur_q0) - int(oracle_q0))
                if tie_delta > int(worst_tie_delta):
                    worst_tie_delta = int(tie_delta)
                    worst_tie_case = {
                        "case": dict(c),
                        "oracle": {"in": int(oracle_in), "q0": int(oracle_q0)},
                        "heuristic": {"in": int(heur_in), "q0": int(heur_q0)},
                        "window": int(window),
                        "bf_max": int(bf_max),
                        "policy_calls": int(policy_calls),
                        "gap": int(gap),
                        "tie_delta": int(tie_delta),
                    }

        match_rate = float(match_count) / float(n)
        avg_calls = float(policy_calls_total) / float(n)

        worst_ok = True
        if worst_calls_max is not None:
            worst_ok = bool(int(worst_calls) <= int(worst_calls_max))

        signal = bool(match_rate >= float(match_min) and avg_calls <= float(avg_calls_max) and worst_ok)
        if signal:
            counterexample = None
        else:
            counterexample = {
                "worst_case": worst_case if worst_case is not None else worst_tie_case,
                "worst_gap": int(worst_gap),
                "worst_tie_case": worst_tie_case,
                "worst_tie_delta": int(worst_tie_delta),
                "worst_calls": int(worst_calls),
                "worst_calls_max": int(worst_calls_max) if worst_calls_max is not None else None,
                "worst_calls_case": worst_calls_case,
            }

        return {
            "status": _mode_status(mode=mode, signal=signal),
            "reason": "ok",
            "signal": signal,
            "counterexample": counterexample,
            "metrics": {
                "policy": str(policy),
                "window": int(window),
                "bf_max": int(bf_max),
                "params": params,
                "oracle_match_rate": float(match_rate),
                "oracle_match_count": int(match_count),
                "oracle_in_match_count": int(in_match_count),
                "tie_mismatch_count": int(tie_mismatch_count),
                "gap_mismatch_count": int(gap_mismatch_count),
                "n": int(n),
                "avg_policy_calls": float(avg_calls),
                "policy_calls_total": int(policy_calls_total),
                "worst_calls": int(worst_calls),
                "worst_calls_max": int(worst_calls_max) if worst_calls_max is not None else None,
                "worst_gap": int(worst_gap),
            },
            "command": cmd,
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": "",
        }
    finally:
        srd._quote_exact_out = orig_quote  # type: ignore[assignment]


def _check_routing_split_case_dynamic(mode: str, timeout_s: int, check_id: str) -> dict[str, Any] | None:
    """
    Deterministic routing check on a *two parallel pools* case: router output should match the brute-force
    2-pool split oracle (same CPMM v8 semantics).

    Formats:
    - routing_split_case_optimal::<profile|default>::x0=..,y0=..,fee0=..,x1=..,y1=..,fee1=..,amount_in=..
      signal := (router_out == brute_out)
    - routing_split_case_gap_exists::<profile|default>::...,min_gap=1
      signal := (brute_out - router_out) >= min_gap
    """
    m = re.match(r"^routing_split_case_(optimal|gap_exists)::([A-Za-z0-9_]+)::(.+)$", check_id)
    if not m:
        return None
    kind = str(m.group(1))
    profile = str(m.group(2))
    params, err = _parse_kv_int_params(str(m.group(3)))
    if err is not None or params is None:
        return {
            "status": "inconclusive",
            "reason": f"bad_params:{err or 'unknown'}",
            "signal": None,
            "counterexample": {"check_id": check_id},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "bad params",
        }

    required = ["x0", "y0", "fee0", "x1", "y1", "fee1", "amount_in"]
    missing = [k for k in required if k not in params]
    if missing:
        return {
            "status": "inconclusive",
            "reason": "missing_params",
            "signal": None,
            "counterexample": {"check_id": check_id, "missing": missing},
            "metrics": {"parsed_params": params, "profile": profile},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "missing params",
        }

    t0 = time.time()
    cmd = ["internal_python_eval", "routing_split_case", kind, profile]
    try:
        import sys  # pylint: disable=import-outside-toplevel

        if str(ROOT) not in sys.path:
            sys.path.insert(0, str(ROOT))
        from src.core.routing import best_route_exact_in_2hop  # pylint: disable=import-outside-toplevel
        from src.state.pools import PoolState, PoolStatus  # pylint: disable=import-outside-toplevel
        from src.core.split_routing import (  # pylint: disable=import-outside-toplevel
            PoolXY,
            brute_force_best_split_two_pools_exact_in,
        )
    except Exception as exc:
        return {
            "status": "inconclusive",
            "reason": "import_error",
            "signal": None,
            "counterexample": {"error": str(exc)},
            "metrics": {"profile": profile, "params": params},
            "command": cmd,
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": str(exc)[-1200:],
        }

    # Router works with PoolState objects; keep pool_ids deterministic.
    p0 = PoolState(
        pool_id="p0",
        asset0="A",
        asset1="B",
        reserve0=int(params["x0"]),
        reserve1=int(params["y0"]),
        fee_bps=int(params["fee0"]),
        lp_supply=1,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )
    p1 = PoolState(
        pool_id="p1",
        asset0="A",
        asset1="B",
        reserve0=int(params["x1"]),
        reserve1=int(params["y1"]),
        fee_bps=int(params["fee1"]),
        lp_supply=1,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )
    pools = {p0.pool_id: p0, p1.pool_id: p1}
    amount_in = int(params["amount_in"])

    # Oracle output for splitting across two parallel pools.
    xy0 = PoolXY(x=int(params["x0"]), y=int(params["y0"]), fee_bps=int(params["fee0"]))
    xy1 = PoolXY(x=int(params["x1"]), y=int(params["y1"]), fee_bps=int(params["fee1"]))
    try:
        brute_out, _brute_a = brute_force_best_split_two_pools_exact_in(xy0, xy1, amount_in)
    except Exception as exc:
        return {
            "status": "inconclusive",
            "reason": "invalid_case",
            "signal": None,
            "counterexample": {"error": str(exc), "profile": profile, "params": params},
            "metrics": {"profile": profile, "params": params},
            "command": cmd,
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": str(exc)[-1200:],
        }

    try:
        if profile == "default":
            q = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=amount_in)
        else:
            q = best_route_exact_in_2hop(
                pools_by_id=pools,
                asset_in="A",
                asset_out="B",
                amount_in=amount_in,
                split_search_profile=str(profile),
            )
    except Exception as exc:
        return {
            "status": "inconclusive",
            "reason": "router_error",
            "signal": None,
            "counterexample": {"error": str(exc), "profile": profile, "params": params},
            "metrics": {"profile": profile, "params": params},
            "command": cmd,
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": str(exc)[-1200:],
        }

    if q is None:
        return {
            "status": "inconclusive",
            "reason": "router_returned_none",
            "signal": None,
            "counterexample": {"profile": profile, "params": params},
            "metrics": {"profile": profile, "params": params, "oracle_out": int(brute_out)},
            "command": cmd,
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": "",
        }

    router_out = int(q.amount_out)
    gap = int(brute_out) - int(router_out)

    if kind == "optimal":
        signal = bool(gap == 0)
        counterexample = None
        if not signal:
            counterexample = {
                "profile": profile,
                "params": params,
                "oracle_out": int(brute_out),
                "router_out": int(router_out),
                "gap": gap,
                "route": {
                    "legs": [
                        {
                            "amount_in": int(leg.amount_in),
                            "amount_out": int(leg.amount_out),
                            "pools": [h.pool_id for h in leg.hops],
                        }
                        for leg in q.legs
                    ]
                },
            }
    else:
        min_gap = int(params.get("min_gap", 1))
        if min_gap <= 0:
            return {
                "status": "inconclusive",
                "reason": "bad_params:min_gap",
                "signal": None,
                "counterexample": {"check_id": check_id, "min_gap": min_gap},
                "metrics": {"profile": profile, "params": params},
                "command": cmd,
                "duration_s": float(time.time() - t0),
                "stdout_tail": "",
                "stderr_tail": "min_gap must be positive",
            }
        signal = bool(gap >= min_gap)
        counterexample = None
        if signal:
            counterexample = {
                "profile": profile,
                "params": params,
                "oracle_out": int(brute_out),
                "router_out": int(router_out),
                "gap": gap,
                "route": {
                    "legs": [
                        {
                            "amount_in": int(leg.amount_in),
                            "amount_out": int(leg.amount_out),
                            "pools": [h.pool_id for h in leg.hops],
                        }
                        for leg in q.legs
                    ]
                },
            }

    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": counterexample,
        "metrics": {
            "kind": kind,
            "profile": profile,
            "params": params,
            "oracle_out": int(brute_out),
            "router_out": int(router_out),
            "gap": gap,
            "leg_count": len(q.legs),
        },
        "command": cmd,
        "duration_s": float(time.time() - t0),
        "stdout_tail": "",
        "stderr_tail": "",
    }


def _check_exact_out_gate_tradeoff_dynamic(mode: str, timeout_s: int, check_id: str) -> dict[str, Any] | None:
    """
    Deterministic tradeoff check for exact-out 2-hop gating.

    Format:
    - exact_out_gate_tradeoff::<policy>::seed=..,n=..,stress_bp=..,pressure_bp=..,capture_bp=..,avg_calls_milli=..

    Interpretation:
    - stress_threshold = stress_bp / 10_000
    - pressure_threshold = pressure_bp / 10_000
    - capture_min = capture_bp / 10_000
    - avg_calls_max = avg_calls_milli / 1_000
    signal := (capture_rate >= capture_min) AND (avg_calls <= avg_calls_max)
    """
    m = re.match(r"^exact_out_gate_tradeoff::([A-Za-z0-9_]+)::(.+)$", check_id)
    if not m:
        return None
    policy = str(m.group(1)).strip()
    params, err = _parse_kv_int_params(str(m.group(2)))
    if err is not None or params is None:
        return {
            "status": "inconclusive",
            "reason": f"bad_params:{err or 'unknown'}",
            "signal": None,
            "counterexample": {"check_id": check_id},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "bad params",
        }

    required = ["seed", "n", "stress_bp", "pressure_bp", "capture_bp", "avg_calls_milli"]
    missing = [k for k in required if k not in params]
    if missing:
        return {
            "status": "inconclusive",
            "reason": "missing_params",
            "signal": None,
            "counterexample": {"check_id": check_id, "missing": missing},
            "metrics": {"parsed_params": params, "policy": policy},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "missing params",
        }

    t0 = time.time()
    cmd = ["internal_python_eval", "exact_out_gate_tradeoff", policy]
    try:
        import random  # pylint: disable=import-outside-toplevel
        import sys  # pylint: disable=import-outside-toplevel

        if str(ROOT) not in sys.path:
            sys.path.insert(0, str(ROOT))
        from src.core.routing import (  # pylint: disable=import-outside-toplevel
            ExactOutTwoHopGateConfig,
            should_consider_exact_out_two_hop,
        )
        from src.kernels.python.cpmm_swap_v8 import swap_exact_out  # pylint: disable=import-outside-toplevel
    except Exception as exc:
        return {
            "status": "inconclusive",
            "reason": "import_error",
            "signal": None,
            "counterexample": {"error": str(exc)},
            "metrics": {"policy": policy, "params": params},
            "command": cmd,
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": str(exc)[-1200:],
        }

    seed = int(params["seed"])
    n = int(params["n"])
    if n <= 0:
        return {
            "status": "inconclusive",
            "reason": "bad_params:n",
            "signal": None,
            "counterexample": {"check_id": check_id, "n": n},
            "metrics": {"policy": policy, "params": params},
            "command": cmd,
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": "n must be positive",
        }

    stress_th = float(int(params["stress_bp"])) / 10_000.0
    pressure_th = float(int(params["pressure_bp"])) / 10_000.0
    capture_min = float(int(params["capture_bp"])) / 10_000.0
    avg_calls_max = float(int(params["avg_calls_milli"])) / 1_000.0

    cfg = ExactOutTwoHopGateConfig(
        policy=str(policy),
        stress_threshold=float(stress_th),
        pressure_threshold=float(pressure_th),
    )

    rng = random.Random(seed)
    feasible = 0
    total_improvement = 0
    capture_improvement = 0
    calls = 0

    for _ in range(n):
        x_ab = rng.randint(40, 400)
        y_ab = rng.randint(40, 400)
        fee_ab = rng.randint(0, 50)
        x_ac = rng.randint(40, 400)
        y_ac = rng.randint(40, 400)
        fee_ac = rng.randint(0, 50)
        x_cb = rng.randint(40, 400)
        y_cb = rng.randint(40, 400)
        fee_cb = rng.randint(0, 50)
        max_out = min(y_ab - 1, y_cb - 1, 120)
        if max_out < 1:
            continue
        amount_out = rng.randint(1, max_out)

        try:
            direct_in = swap_exact_out(reserve_in=x_ab, reserve_out=y_ab, amount_out=amount_out, fee_bps=fee_ab).amount_in
            mid_in = swap_exact_out(reserve_in=x_cb, reserve_out=y_cb, amount_out=amount_out, fee_bps=fee_cb).amount_in
            two_hop_in = swap_exact_out(reserve_in=x_ac, reserve_out=y_ac, amount_out=mid_in, fee_bps=fee_ac).amount_in
        except Exception:
            continue

        feasible += 1
        win = int(two_hop_in) < int(direct_in)
        improvement = int(direct_in - two_hop_in) if win else 0
        total_improvement += improvement

        use_two_hop = should_consider_exact_out_two_hop(
            amount_out=int(amount_out),
            direct_reserve_out=int(y_ab),
            direct_amount_in=int(direct_in),
            config=cfg,
        )
        calls += 3 if use_two_hop else 1

        if win and use_two_hop:
            capture_improvement += improvement

    if feasible <= 0 or total_improvement <= 0:
        return {
            "status": "inconclusive",
            "reason": "no_feasible_cases",
            "signal": None,
            "counterexample": {"policy": policy, "params": params, "feasible": feasible, "total_improvement": total_improvement},
            "metrics": {"policy": policy, "params": params},
            "command": cmd,
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": "",
        }

    capture_rate = float(capture_improvement) / float(total_improvement)
    avg_calls = float(calls) / float(feasible)

    signal = bool(capture_rate >= float(capture_min) and avg_calls <= float(avg_calls_max))
    counterexample = None
    if not signal:
        counterexample = {
            "policy": policy,
            "params": params,
            "capture_rate": capture_rate,
            "avg_calls": avg_calls,
            "capture_min": capture_min,
            "avg_calls_max": avg_calls_max,
        }

    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": counterexample,
        "metrics": {
            "policy": policy,
            "seed": seed,
            "n": n,
            "feasible": feasible,
            "stress_threshold": stress_th,
            "pressure_threshold": pressure_th,
            "capture_min": capture_min,
            "avg_calls_max": avg_calls_max,
            "capture_rate": capture_rate,
            "avg_calls": avg_calls,
        },
        "command": cmd,
        "duration_s": float(time.time() - t0),
        "stdout_tail": "",
        "stderr_tail": "",
    }


def _check_split_routing_gap(mode: str, timeout_s: int) -> dict[str, Any]:
    cmd = ["python3", "tools/morph_split_routing_miner.py", "--mine", "--json", "--seed", "7"]
    cmd_res = _run_cmd(cmd, timeout_s=timeout_s)
    if cmd_res.timeout:
        return {
            "status": "inconclusive",
            "reason": "timeout",
            "signal": None,
            "counterexample": None,
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    payload = _extract_json(cmd_res.stdout)
    if not cmd_res.ok or payload is None:
        return {
            "status": "inconclusive",
            "reason": "command_error_or_unparseable_json",
            "signal": None,
            "counterexample": None,
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    outcome = str(payload.get("outcome", ""))
    target_gap = int(payload.get("target_gap", 0))
    witness = str(payload.get("witness", "")).strip()
    has_gap_witness = outcome == "KernelSolved" and bool(witness) and target_gap >= 1
    counterexample = {"witness": witness, "target_gap": target_gap} if has_gap_witness else None
    return {
        "status": _mode_status(mode=mode, signal=has_gap_witness),
        "reason": "ok",
        "signal": bool(has_gap_witness),
        "counterexample": counterexample,
        "metrics": {"target_gap": target_gap, "outcome": outcome},
        "command": cmd,
        "duration_s": cmd_res.duration_s,
        "stdout_tail": cmd_res.stdout[-1200:],
        "stderr_tail": cmd_res.stderr[-1200:],
    }


def _check_twap_staleness_effect(mode: str, timeout_s: int) -> dict[str, Any]:
    cmd = ["python3", "tools/morph_twap_manipulation_miner.py", "--test", "--json"]
    cmd_res = _run_cmd(cmd, timeout_s=timeout_s)
    if cmd_res.timeout:
        return {
            "status": "inconclusive",
            "reason": "timeout",
            "signal": None,
            "counterexample": None,
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    payload = _extract_json(cmd_res.stdout)
    if not cmd_res.ok or payload is None:
        return {
            "status": "inconclusive",
            "reason": "command_error_or_unparseable_json",
            "signal": None,
            "counterexample": None,
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }

    rows = (((payload.get("no_deviation_limits") or {}).get("results_by_stale_window")) or [])
    by_window: dict[int, float] = {}
    for row in rows:
        try:
            by_window[int(row["stale_window"])] = float(row["deviation_pct"])
        except Exception:
            continue
    d60 = by_window.get(60)
    d3600 = by_window.get(3600)
    if d60 is None or d3600 is None:
        return {
            "status": "inconclusive",
            "reason": "missing_stale_window_metrics",
            "signal": None,
            "counterexample": None,
            "metrics": {"deviation_by_window": by_window},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }

    # Signal: tighter staleness window materially reduces manipulation deviation.
    signal = bool((d3600 - d60) >= 10.0 and d60 < d3600)
    counterexample = None
    if signal:
        counterexample = {
            "deviation_60s_pct": d60,
            "deviation_3600s_pct": d3600,
            "delta_pct": float(d3600 - d60),
        }
    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": counterexample,
        "metrics": {"deviation_by_window": by_window},
        "command": cmd,
        "duration_s": cmd_res.duration_s,
        "stdout_tail": cmd_res.stdout[-1200:],
        "stderr_tail": cmd_res.stderr[-1200:],
    }


def _check_perp_clamp_profit(mode: str, timeout_s: int) -> dict[str, Any]:
    cmd = [
        "python3",
        "tools/perp_oracle_manipulation_sweep.py",
        "--reserves",
        "100,200",
        "--fee-bps",
        "10,30",
        "--max-move-bps",
        "50,100",
        "--max-pos-abs",
        "50,100",
        "--max-trade-in",
        "100",
    ]
    cmd_res = _run_cmd(cmd, timeout_s=timeout_s)
    if cmd_res.timeout:
        return {
            "status": "inconclusive",
            "reason": "timeout",
            "signal": None,
            "counterexample": None,
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    payload = _extract_json(cmd_res.stdout)
    if not cmd_res.ok or payload is None:
        return {
            "status": "inconclusive",
            "reason": "command_error_or_unparseable_json",
            "signal": None,
            "counterexample": None,
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    rows = payload.get("results")
    if not isinstance(rows, list) or not rows:
        return {
            "status": "inconclusive",
            "reason": "missing_results",
            "signal": None,
            "counterexample": None,
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    best_by_move: dict[int, float] = {}
    for row in rows:
        try:
            mm = int(row["max_move_bps"])
            prof = float(row["net_profit_quote"])
        except Exception:
            continue
        cur = best_by_move.get(mm)
        if cur is None or prof > cur:
            best_by_move[mm] = prof
    p50 = best_by_move.get(50)
    p100 = best_by_move.get(100)
    if p50 is None or p100 is None:
        return {
            "status": "inconclusive",
            "reason": "missing_move_buckets",
            "signal": None,
            "counterexample": None,
            "metrics": {"best_profit_by_max_move_bps": best_by_move},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }

    # Signal: tighter clamp (50bps) yields lower or equal best attack profit and is strictly better in at least one bucket.
    signal = bool(p50 <= p100 and p50 < p100)
    counterexample = None
    if signal:
        counterexample = {
            "best_profit_50bps": p50,
            "best_profit_100bps": p100,
            "improvement_quote": float(p100 - p50),
        }
    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": counterexample,
        "metrics": {"best_profit_by_max_move_bps": best_by_move},
        "command": cmd,
        "duration_s": cmd_res.duration_s,
        "stdout_tail": cmd_res.stdout[-1200:],
        "stderr_tail": cmd_res.stderr[-1200:],
    }


def _check_batch_greedy_invariants(mode: str, timeout_s: int) -> dict[str, Any]:
    return _check_pytest_file(mode, timeout_s, "tests/core/test_batch_greedy.py")


def _check_esso_cpmm_verify(mode: str, timeout_s: int) -> dict[str, Any]:
    cmd = [
        "bash",
        "-lc",
        (
            "cd "
            + shlex.quote(str(ROOT))
            + " && PYTHONPATH=external/ESSO python3 -m ESSO verify-multi "
            + "src/kernels/dex/cpmm_swap.yaml --solvers cvc5 --timeout-ms 30000 --determinism-trials 2"
        ),
    ]
    cmd_res = _run_cmd(cmd, timeout_s=timeout_s)
    if cmd_res.timeout:
        return {
            "status": "inconclusive",
            "reason": "timeout",
            "signal": None,
            "counterexample": None,
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    payload = _extract_json(cmd_res.stdout)
    if payload is None:
        return {
            "status": "inconclusive",
            "reason": "unparseable_json",
            "signal": None,
            "counterexample": None,
            "metrics": {"returncode": cmd_res.returncode},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    verdict = str((payload.get("report") or {}).get("verdict", ""))
    signal = bool(cmd_res.ok and payload.get("ok") is True and verdict == "VERIFIED")
    counterexample = None if signal else {"verify_report": payload}
    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": counterexample,
        "metrics": {"verdict": verdict, "ok": payload.get("ok")},
        "command": cmd,
        "duration_s": cmd_res.duration_s,
        "stdout_tail": cmd_res.stdout[-1200:],
        "stderr_tail": cmd_res.stderr[-1200:],
    }


def _check_lean_batch_canonical(mode: str, timeout_s: int) -> dict[str, Any]:
    cmd = [
        "bash",
        "-lc",
        f"cd {shlex.quote(str(ROOT / 'lean-mathlib'))} && lake env lean Proofs/BatchAuctionCanonical.lean",
    ]
    cmd_res = _run_cmd(cmd, timeout_s=timeout_s)
    if cmd_res.timeout:
        return {
            "status": "inconclusive",
            "reason": "timeout",
            "signal": None,
            "counterexample": None,
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    err_text = (cmd_res.stdout + "\n" + cmd_res.stderr).lower()
    if ("package directory not found" in err_text and "mathlib" in err_text) or ("manifest out of date" in err_text and "mathlib" in err_text and not cmd_res.ok):
        return {
            "status": "inconclusive",
            "reason": "mathlib_not_wired",
            "signal": None,
            "counterexample": None,
            "metrics": {"returncode": cmd_res.returncode},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    signal = bool(cmd_res.ok)
    counterexample = None if signal else {"lean_output_tail": (cmd_res.stdout + "\n" + cmd_res.stderr)[-1200:]}
    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": counterexample,
        "metrics": {"returncode": cmd_res.returncode},
        "command": cmd,
        "duration_s": cmd_res.duration_s,
        "stdout_tail": cmd_res.stdout[-1200:],
        "stderr_tail": cmd_res.stderr[-1200:],
    }


def _check_roundtrip_no_positive_profit(mode: str, timeout_s: int) -> dict[str, Any]:
    cmd = [
        "python3",
        "tools/curve_roundtrip_profit_sweep.py",
        "--grid-min",
        "1",
        "--grid-max",
        "30",
        "--grid-step",
        "2",
        "--dx",
        "1,2,5",
        "--no-quadratic",
    ]
    cmd_res = _run_cmd(cmd, timeout_s=timeout_s)
    if cmd_res.timeout:
        return {
            "status": "inconclusive",
            "reason": "timeout",
            "signal": None,
            "counterexample": None,
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    payload = _extract_json(cmd_res.stdout)
    if not cmd_res.ok or payload is None:
        return {
            "status": "inconclusive",
            "reason": "command_error_or_unparseable_json",
            "signal": None,
            "counterexample": None,
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    rows = (((payload.get("roundtrip") or {}).get("results")) or {})
    if not isinstance(rows, dict) or not rows:
        return {
            "status": "inconclusive",
            "reason": "missing_roundtrip_results",
            "signal": None,
            "counterexample": None,
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    max_profit_by_curve: dict[str, float] = {}
    for curve, vals in rows.items():
        try:
            max_profit_by_curve[str(curve)] = float(vals.get("profit_max"))
        except Exception:
            continue
    signal = bool(max_profit_by_curve and all(v <= 0.0 for v in max_profit_by_curve.values()))
    counterexample = None
    if not signal:
        bad = [{"curve": k, "profit_max": v} for k, v in max_profit_by_curve.items() if v > 0.0]
        counterexample = {"profitable_roundtrip_curves": bad}
    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": counterexample,
        "metrics": {"max_profit_by_curve": max_profit_by_curve},
        "command": cmd,
        "duration_s": cmd_res.duration_s,
        "stdout_tail": cmd_res.stdout[-1200:],
        "stderr_tail": cmd_res.stderr[-1200:],
    }


def _check_lp_rounding_tests(mode: str, timeout_s: int) -> dict[str, Any]:
    cmd = ["python3", "tools/morph_lp_rounding_miner.py", "--test", "--json"]
    cmd_res = _run_cmd(cmd, timeout_s=timeout_s)
    if cmd_res.timeout:
        return {
            "status": "inconclusive",
            "reason": "timeout",
            "signal": None,
            "counterexample": None,
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    payload = _extract_json(cmd_res.stdout)
    if not cmd_res.ok or payload is None:
        return {
            "status": "inconclusive",
            "reason": "command_error_or_unparseable_json",
            "signal": None,
            "counterexample": None,
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    failed = int(payload.get("tests_failed", 1_000_000))
    passed = int(payload.get("tests_passed", 0))
    all_passed = bool(payload.get("all_passed", False))
    signal = bool(all_passed and failed == 0 and passed >= 1)
    counterexample = None if signal else {"lp_rounding_report": payload}
    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": counterexample,
        "metrics": {"tests_passed": passed, "tests_failed": failed, "all_passed": all_passed},
        "command": cmd,
        "duration_s": cmd_res.duration_s,
        "stdout_tail": cmd_res.stdout[-1200:],
        "stderr_tail": cmd_res.stderr[-1200:],
    }


def _check_settlement_normal_form(mode: str, timeout_s: int) -> dict[str, Any]:
    cmd = ["python3", "tools/morph_settlement_normal_form_miner.py", "--test", "--json"]
    cmd_res = _run_cmd(cmd, timeout_s=timeout_s)
    if cmd_res.timeout:
        return {
            "status": "inconclusive",
            "reason": "timeout",
            "signal": None,
            "counterexample": None,
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    payload = _extract_json(cmd_res.stdout)
    if not cmd_res.ok or payload is None:
        return {
            "status": "inconclusive",
            "reason": "command_error_or_unparseable_json",
            "signal": None,
            "counterexample": None,
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    none_vs_zero = bool(((payload.get("none_vs_zero") or {}).get("passed")))
    duplicate_ok = bool(((payload.get("duplicate_deltas") or {}).get("passed")))
    normalized_equal = bool(((payload.get("duplicate_deltas") or {}).get("normalized_forms_equal")))
    missing_keys_ok = bool(((payload.get("missing_keys") or {}).get("passed")))
    fill_ordering_ok = bool(((payload.get("fill_ordering") or {}).get("passed")))
    same_normalized = bool(((payload.get("fill_ordering") or {}).get("same_normalized")))
    signal = bool(none_vs_zero and duplicate_ok and normalized_equal and missing_keys_ok and fill_ordering_ok and same_normalized)
    counterexample = None if signal else {"settlement_normal_form_report": payload}
    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": counterexample,
        "metrics": {
            "none_vs_zero": none_vs_zero,
            "duplicate_deltas": duplicate_ok,
            "normalized_forms_equal": normalized_equal,
            "missing_keys": missing_keys_ok,
            "fill_ordering": fill_ordering_ok,
            "same_normalized": same_normalized,
        },
        "command": cmd,
        "duration_s": cmd_res.duration_s,
        "stdout_tail": cmd_res.stdout[-1200:],
        "stderr_tail": cmd_res.stderr[-1200:],
    }


def _check_il_insurance_vuln_presence(mode: str, timeout_s: int) -> dict[str, Any]:
    cmd = ["python3", "tools/morph_il_insurance_miner.py", "--test", "--json"]
    cmd_res = _run_cmd(cmd, timeout_s=timeout_s)
    if cmd_res.timeout:
        return {
            "status": "inconclusive",
            "reason": "timeout",
            "signal": None,
            "counterexample": None,
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    payload = _extract_json(cmd_res.stdout)
    if not cmd_res.ok or payload is None:
        return {
            "status": "inconclusive",
            "reason": "command_error_or_unparseable_json",
            "signal": None,
            "counterexample": None,
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    findings = payload.get("findings") or []
    severities: set[str] = set()
    for row in findings:
        if isinstance(row, list) and row:
            severities.add(str(row[0]))
        if isinstance(row, dict):
            severities.add(str(row.get("severity", "")))
    has_critical = "CRITICAL" in severities
    has_high = "HIGH" in severities
    signal = bool(has_critical or has_high)
    counterexample = None if signal else {"findings": findings}
    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": counterexample,
        "metrics": {
            "has_critical": has_critical,
            "has_high": has_high,
            "finding_count": int(payload.get("finding_count", 0)),
            "all_assertions_passed": bool(payload.get("all_assertions_passed", False)),
        },
        "command": cmd,
        "duration_s": cmd_res.duration_s,
        "stdout_tail": cmd_res.stdout[-1200:],
        "stderr_tail": cmd_res.stderr[-1200:],
    }


def _check_route_exact_out_2hop_value(mode: str, timeout_s: int) -> dict[str, Any]:
    t0 = time.time()
    cmd = ["internal_python_eval", "route_exact_out_2hop_value"]
    try:
        import sys  # pylint: disable=import-outside-toplevel

        if str(ROOT) not in sys.path:
            sys.path.insert(0, str(ROOT))
        from tools.morph_route_exact_out_2hop_value_miner import (  # pylint: disable=import-outside-toplevel
            Route2HopValueCase,
            eval_route_exact_out_2hop_value_python,
            eval_route_exact_out_2hop_value_z3,
        )
    except Exception as exc:
        return {
            "status": "inconclusive",
            "reason": "import_error",
            "signal": None,
            "counterexample": {"error": str(exc)},
            "metrics": {},
            "command": cmd,
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": str(exc)[-1200:],
        }
    case = Route2HopValueCase(
        x_ab=2,
        y_ab=2,
        fee_ab=0,
        x_ac=1,
        y_ac=2,
        fee_ac=0,
        x_cb=1,
        y_cb=2,
        fee_cb=0,
        amount_out=1,
    )
    ok_py, py_details = eval_route_exact_out_2hop_value_python(case)
    ok_z3, z3_details = eval_route_exact_out_2hop_value_z3(case)
    py_twohop = int((py_details or {}).get("twohop_in", 1_000_000_000))
    py_direct = int((py_details or {}).get("direct_in", -1))
    signal = bool(ok_py and ok_z3 and py_twohop < py_direct)
    counterexample = None
    if signal:
        counterexample = {
            "witness": {
                "x_ab": 2,
                "y_ab": 2,
                "fee_ab": 0,
                "x_ac": 1,
                "y_ac": 2,
                "fee_ac": 0,
                "x_cb": 1,
                "y_cb": 2,
                "fee_cb": 0,
                "amount_out": 1,
            },
            "python": py_details,
            "z3": z3_details,
        }
    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": counterexample,
        "metrics": {
            "python_checker_ok": bool(ok_py),
            "z3_checker_ok": bool(ok_z3),
            "python_details": py_details,
            "z3_details": z3_details,
        },
        "command": cmd,
        "duration_s": float(time.time() - t0),
        "stdout_tail": "",
        "stderr_tail": "",
    }


def _count_split_profile_calls(
    *,
    pool0: Any,
    pool1: Any,
    amount_in: int,
    search_profile: str,
) -> tuple[tuple[int, int], int]:
    import src.core.split_routing as sr  # pylint: disable=import-outside-toplevel

    orig = sr.exact_out_for_pool_exact_in
    calls = {"n": 0}

    def wrapped(pool: Any, amount: int) -> int:
        calls["n"] = int(calls["n"]) + 1
        return orig(pool, amount)

    sr.exact_out_for_pool_exact_in = wrapped  # type: ignore[assignment]
    try:
        result = sr.best_split_two_pools_exact_in(
            pool0,
            pool1,
            int(amount_in),
            window=64,
            search_profile=str(search_profile),
        )
    finally:
        sr.exact_out_for_pool_exact_in = orig  # type: ignore[assignment]
    return result, int(calls["n"])


def _check_dgstr_exact_match(mode: str, timeout_s: int) -> dict[str, Any]:
    del timeout_s  # deterministic in-process check
    t0 = time.time()
    cmd = ["internal_python_eval", "dgstr_exact_match"]
    try:
        import sys  # pylint: disable=import-outside-toplevel

        if str(ROOT) not in sys.path:
            sys.path.insert(0, str(ROOT))
        from src.core.split_routing import (  # pylint: disable=import-outside-toplevel
            best_split_two_pools_exact_in,
            brute_force_best_split_two_pools_exact_in,
        )
        from tools.metamuse_split_routing_lane import DGSTR_CURATED_CASES  # pylint: disable=import-outside-toplevel
    except Exception as exc:
        return {
            "status": "inconclusive",
            "reason": "import_error",
            "signal": None,
            "counterexample": {"error": str(exc)},
            "metrics": {},
            "command": cmd,
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": str(exc)[-1200:],
        }

    rows: list[dict[str, Any]] = []
    mismatch: dict[str, Any] | None = None
    for idx, case in enumerate(DGSTR_CURATED_CASES, 1):
        brute = brute_force_best_split_two_pools_exact_in(case.pool0, case.pool1, int(case.amount_in))
        got = best_split_two_pools_exact_in(case.pool0, case.pool1, int(case.amount_in), window=64, search_profile="dgstr_v1")
        row = {
            "case_index": int(idx),
            "amount_in": int(case.amount_in),
            "expected": {"amount_out": int(brute[0]), "split_a": int(brute[1])},
            "got": {"amount_out": int(got[0]), "split_a": int(got[1])},
        }
        rows.append(row)
        if brute != got and mismatch is None:
            mismatch = row

    signal = mismatch is None
    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": None if signal else mismatch,
        "metrics": {"case_count": len(rows), "matched": len(rows) if signal else len(rows) - 1, "rows": rows},
        "command": cmd,
        "duration_s": float(time.time() - t0),
        "stdout_tail": "",
        "stderr_tail": "",
    }


def _check_dgstr_eval_count(mode: str, timeout_s: int) -> dict[str, Any]:
    del timeout_s  # deterministic in-process check
    t0 = time.time()
    cmd = ["internal_python_eval", "dgstr_eval_count"]
    try:
        import sys  # pylint: disable=import-outside-toplevel

        if str(ROOT) not in sys.path:
            sys.path.insert(0, str(ROOT))
        from tools.metamuse_split_routing_lane import DGSTR_CURATED_CASES  # pylint: disable=import-outside-toplevel
    except Exception as exc:
        return {
            "status": "inconclusive",
            "reason": "import_error",
            "signal": None,
            "counterexample": {"error": str(exc)},
            "metrics": {},
            "command": cmd,
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": str(exc)[-1200:],
        }

    rows: list[dict[str, Any]] = []
    dgstr_calls_total = 0
    base_calls_total = 0
    mismatch: dict[str, Any] | None = None
    for idx, case in enumerate(DGSTR_CURATED_CASES, 1):
        dgstr_result, dgstr_calls = _count_split_profile_calls(
            pool0=case.pool0,
            pool1=case.pool1,
            amount_in=int(case.amount_in),
            search_profile="dgstr_v1",
        )
        base_result, base_calls = _count_split_profile_calls(
            pool0=case.pool0,
            pool1=case.pool1,
            amount_in=int(case.amount_in),
            search_profile="baseline_canon16",
        )
        row = {
            "case_index": int(idx),
            "amount_in": int(case.amount_in),
            "dgstr": {"result": {"amount_out": int(dgstr_result[0]), "split_a": int(dgstr_result[1])}, "calls": int(dgstr_calls)},
            "baseline_canon16": {"result": {"amount_out": int(base_result[0]), "split_a": int(base_result[1])}, "calls": int(base_calls)},
        }
        rows.append(row)
        if dgstr_result != base_result and mismatch is None:
            mismatch = row
        dgstr_calls_total += int(dgstr_calls)
        base_calls_total += int(base_calls)

    signal = bool(
        mismatch is None
        and dgstr_calls_total < base_calls_total
        and dgstr_calls_total * 4 <= base_calls_total * 3
    )
    counterexample = mismatch
    if counterexample is None and not signal:
        counterexample = {
            "dgstr_calls_total": int(dgstr_calls_total),
            "baseline_calls_total": int(base_calls_total),
        }
    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": counterexample,
        "metrics": {
            "case_count": len(rows),
            "dgstr_calls_total": int(dgstr_calls_total),
            "baseline_calls_total": int(base_calls_total),
            "dgstr_calls_mean": float(dgstr_calls_total) / float(max(1, len(rows))),
            "baseline_calls_mean": float(base_calls_total) / float(max(1, len(rows))),
            "rows": rows,
        },
        "command": cmd,
        "duration_s": float(time.time() - t0),
        "stdout_tail": "",
        "stderr_tail": "",
    }


def _check_batch_mci_vs_bruteforce(mode: str, timeout_s: int) -> dict[str, Any]:
    del timeout_s  # deterministic in-process check
    t0 = time.time()
    cmd = ["internal_python_eval", "batch_mci_vs_bruteforce"]
    try:
        import sys  # pylint: disable=import-outside-toplevel

        if str(ROOT) not in sys.path:
            sys.path.insert(0, str(ROOT))
        from src.core.batch_clearing import (  # pylint: disable=import-outside-toplevel
            _eval_ordering_ab,
            _order_swaps_mci_ab,
            _order_swaps_optimal_ab_bounded,
            _refine_ab_ordering_global,
        )
        from tools.metamuse_batch_ordering_lane import (  # pylint: disable=import-outside-toplevel
            BATCH_MCI_CURATED_CASES,
            build_case_balances,
            build_case_pool_and_intents,
        )
    except Exception as exc:
        return {
            "status": "inconclusive",
            "reason": "import_error",
            "signal": None,
            "counterexample": {"error": str(exc)},
            "metrics": {},
            "command": cmd,
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": str(exc)[-1200:],
        }

    rows: list[dict[str, Any]] = []
    mismatch: dict[str, Any] | None = None
    for idx, case in enumerate(BATCH_MCI_CURATED_CASES, 1):
        pool, intents = build_case_pool_and_intents(case)
        balances = build_case_balances(case)
        reserves = (pool.reserve0, pool.reserve1)
        mci_seed = _order_swaps_mci_ab(intents, pool_state=pool, reserves=reserves)
        mci_order = _refine_ab_ordering_global(mci_seed, pool_state=pool, reserves=reserves)
        optimal_order = _order_swaps_optimal_ab_bounded(
            intents,
            pool_state=pool,
            balances=balances,
            reserves=reserves,
        )
        mci_ab = tuple(int(x) for x in _eval_ordering_ab(mci_order, pool, reserves))
        optimal_ab = tuple(int(x) for x in _eval_ordering_ab(optimal_order, pool, reserves))
        row = {
            "case_index": int(idx),
            "expected_ab": {"A": int(case.expected_ab[0]), "B": int(case.expected_ab[1])},
            "mci_ab_global": {"A": int(mci_ab[0]), "B": int(mci_ab[1])},
            "optimal_ab_bounded": {"A": int(optimal_ab[0]), "B": int(optimal_ab[1])},
        }
        rows.append(row)
        if mismatch is None and (mci_ab != case.expected_ab or optimal_ab != case.expected_ab):
            mismatch = row

    signal = mismatch is None
    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": mismatch,
        "metrics": {"case_count": len(rows), "matched": len(rows) if signal else len(rows) - 1, "rows": rows},
        "command": cmd,
        "duration_s": float(time.time() - t0),
        "stdout_tail": "",
        "stderr_tail": "",
    }


def _check_batch_mci_vs_greedy(mode: str, timeout_s: int) -> dict[str, Any]:
    del timeout_s  # deterministic in-process check
    t0 = time.time()
    cmd = ["internal_python_eval", "batch_mci_vs_greedy"]
    try:
        import sys  # pylint: disable=import-outside-toplevel

        if str(ROOT) not in sys.path:
            sys.path.insert(0, str(ROOT))
        from src.core.batch_clearing import (  # pylint: disable=import-outside-toplevel
            _eval_ordering_ab,
            _order_swaps_greedy_ab,
            _order_swaps_mci_ab,
            _refine_ab_ordering_global,
            _refine_b_ordering,
        )
        from tools.metamuse_batch_ordering_lane import (  # pylint: disable=import-outside-toplevel
            BATCH_MCI_CURATED_CASES,
            build_case_pool_and_intents,
        )
    except Exception as exc:
        return {
            "status": "inconclusive",
            "reason": "import_error",
            "signal": None,
            "counterexample": {"error": str(exc)},
            "metrics": {},
            "command": cmd,
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": str(exc)[-1200:],
        }

    rows: list[dict[str, Any]] = []
    mismatch: dict[str, Any] | None = None
    improvement_count = 0
    for idx, case in enumerate(BATCH_MCI_CURATED_CASES, 1):
        pool, intents = build_case_pool_and_intents(case)
        reserves = (pool.reserve0, pool.reserve1)
        mci_seed = _order_swaps_mci_ab(intents, pool_state=pool, reserves=reserves)
        mci_order = _refine_ab_ordering_global(mci_seed, pool_state=pool, reserves=reserves)
        greedy_seed = _order_swaps_greedy_ab(intents, pool_state=pool, reserves=reserves)
        greedy_order = _refine_ab_ordering_global(
            _refine_b_ordering(greedy_seed, pool_state=pool, reserves=reserves),
            pool_state=pool,
            reserves=reserves,
        )
        mci_ab = tuple(int(x) for x in _eval_ordering_ab(mci_order, pool, reserves))
        greedy_ab = tuple(int(x) for x in _eval_ordering_ab(greedy_order, pool, reserves))
        row = {
            "case_index": int(idx),
            "expected_ab": {"A": int(case.expected_ab[0]), "B": int(case.expected_ab[1])},
            "baseline_ab": {"A": int(case.baseline_ab[0]), "B": int(case.baseline_ab[1])},
            "mci_ab_global": {"A": int(mci_ab[0]), "B": int(mci_ab[1])},
            "greedy_ab_global": {"A": int(greedy_ab[0]), "B": int(greedy_ab[1])},
        }
        rows.append(row)
        if mci_ab > greedy_ab:
            improvement_count += 1
        if mismatch is None and (mci_ab != case.expected_ab or greedy_ab != case.baseline_ab or not (mci_ab > greedy_ab)):
            mismatch = row

    signal = mismatch is None and improvement_count == len(rows)
    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": mismatch,
        "metrics": {
            "case_count": len(rows),
            "improvement_count": int(improvement_count),
            "rows": rows,
        },
        "command": cmd,
        "duration_s": float(time.time() - t0),
        "stdout_tail": "",
        "stderr_tail": "",
    }


def _check_burn_receipt_replay_rejected(mode: str, timeout_s: int) -> dict[str, Any]:
    del timeout_s  # deterministic in-process check
    t0 = time.time()
    cmd = ["internal_python_eval", "burn_receipt_replay_rejected"]
    try:
        import sys  # pylint: disable=import-outside-toplevel

        if str(ROOT) not in sys.path:
            sys.path.insert(0, str(ROOT))
        from tools.metamuse_burn_receipt_lane import (  # pylint: disable=import-outside-toplevel
            BURN_RECEIPT_CURATED_STEPS,
            verify_burn_receipt_step,
        )
    except Exception as exc:
        return {
            "status": "inconclusive",
            "reason": "import_error",
            "signal": None,
            "counterexample": {"error": str(exc)},
            "metrics": {},
            "command": cmd,
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": str(exc)[-1200:],
        }

    replay_step = BURN_RECEIPT_CURATED_STEPS[1]
    pass_step = BURN_RECEIPT_CURATED_STEPS[0]
    replay_ok = verify_burn_receipt_step(replay_step)
    pass_ok = verify_burn_receipt_step(pass_step)
    signal = (not replay_ok) and pass_ok
    counterexample = None if signal else {"replay_ok": replay_ok, "pass_ok": pass_ok}
    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": counterexample,
        "metrics": {"replay_expected": 0, "replay_got": int(replay_ok), "pass_expected": 1, "pass_got": int(pass_ok)},
        "command": cmd,
        "duration_s": float(time.time() - t0),
        "stdout_tail": "",
        "stderr_tail": "",
    }


def _check_burn_receipt_accounting_model(mode: str, timeout_s: int) -> dict[str, Any]:
    del timeout_s  # deterministic in-process check
    t0 = time.time()
    cmd = ["internal_python_eval", "burn_receipt_accounting_model"]
    try:
        import sys  # pylint: disable=import-outside-toplevel

        if str(ROOT) not in sys.path:
            sys.path.insert(0, str(ROOT))
        from tools.metamuse_burn_receipt_lane import (  # pylint: disable=import-outside-toplevel
            BURN_RECEIPT_CURATED_STEPS,
            verify_burn_receipt_step,
        )
    except Exception as exc:
        return {
            "status": "inconclusive",
            "reason": "import_error",
            "signal": None,
            "counterexample": {"error": str(exc)},
            "metrics": {},
            "command": cmd,
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": str(exc)[-1200:],
        }

    rows: list[dict[str, Any]] = []
    mismatch: dict[str, Any] | None = None
    accepted_burn_sum = 0
    accepted_batch_delta_sum = 0
    for idx, step in enumerate(BURN_RECEIPT_CURATED_STEPS, 1):
        got = int(1 if verify_burn_receipt_step(step) else 0)
        row = {"case_index": int(idx), "expected_valid": int(step.expected_valid), "got_valid": int(got)}
        rows.append(row)
        if got == 1:
            accepted_burn_sum += int(step.burn_amount)
            accepted_batch_delta_sum += int(step.batch_burn_sum_after) - int(step.batch_burn_sum_before)
        if mismatch is None and got != int(step.expected_valid):
            mismatch = row

    signal = mismatch is None and accepted_burn_sum == accepted_batch_delta_sum
    if mismatch is None and not signal:
        mismatch = {
            "accepted_burn_sum": int(accepted_burn_sum),
            "accepted_batch_delta_sum": int(accepted_batch_delta_sum),
        }
    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": mismatch,
        "metrics": {
            "case_count": len(rows),
            "accepted_burn_sum": int(accepted_burn_sum),
            "accepted_batch_delta_sum": int(accepted_batch_delta_sum),
            "rows": rows,
        },
        "command": cmd,
        "duration_s": float(time.time() - t0),
        "stdout_tail": "",
        "stderr_tail": "",
    }


def _check_sealed_bid_private_state_surface_safe(mode: str, timeout_s: int) -> dict[str, Any]:
    del timeout_s
    t0 = time.time()
    cmd = ["internal_python_eval", "sealed_bid_private_state_surface_safe"]
    try:
        import sys
        if str(ROOT) not in sys.path:
            sys.path.insert(0, str(ROOT))
        from src.core.sealed_bid_auction import RevealedSealedBid, make_sealed_bid_commit_receipt, settle_uniform_price_sealed_bids
        from tools.metamuse_sealed_bid_lane import SEALED_BID_CURATED_CASES
    except Exception as exc:
        return {
            "status": "inconclusive",
            "reason": "import_error",
            "signal": None,
            "counterexample": {"error": str(exc)},
            "metrics": {},
            "command": cmd,
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": str(exc)[-1200:],
        }

    unsafe_case: dict[str, Any] | None = None
    rows: list[dict[str, Any]] = []
    for idx, case in enumerate(SEALED_BID_CURATED_CASES, 1):
        receipts = [
            make_sealed_bid_commit_receipt(
                batch_id=case.batch_id,
                bidder_id=bid.bidder_id,
                commitment=bid.commitment,
                commit_epoch=1,
                reveal_deadline_epoch=2,
                units_for_sale=case.units_for_sale,
            )
            for bid in case.bids
        ]
        leaked = any(any(k in r["body"] for k in ("quantity", "limit_price", "nonce")) for r in receipts)
        revealed = [
            RevealedSealedBid(bidder_id=bid.bidder_id, commitment=bid.commitment, quantity=bid.quantity, limit_price=bid.limit_price)
            for bid in case.bids
        ]
        s1 = settle_uniform_price_sealed_bids(units_for_sale=case.units_for_sale, bids=revealed)
        s2 = settle_uniform_price_sealed_bids(units_for_sale=case.units_for_sale, bids=list(reversed(revealed)))
        nondeterministic = (s1.clearing_price != s2.clearing_price) or ([ (f.bidder_id, f.filled_quantity) for f in s1.fills ] != [ (f.bidder_id, f.filled_quantity) for f in s2.fills ])
        row = {
            "case_index": int(idx),
            "leaked": bool(leaked),
            "nondeterministic": bool(nondeterministic),
        }
        rows.append(row)
        if unsafe_case is None and (leaked or nondeterministic):
            unsafe_case = row

    signal = unsafe_case is None
    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": unsafe_case,
        "metrics": {"case_count": len(rows), "rows": rows},
        "command": cmd,
        "duration_s": float(time.time() - t0),
        "stdout_tail": "",
        "stderr_tail": "",
    }


def _check_sealed_bid_uniform_price_model(mode: str, timeout_s: int) -> dict[str, Any]:
    del timeout_s
    t0 = time.time()
    cmd = ["internal_python_eval", "sealed_bid_uniform_price_model"]
    try:
        import sys
        if str(ROOT) not in sys.path:
            sys.path.insert(0, str(ROOT))
        from tools.metamuse_sealed_bid_lane import SEALED_BID_CURATED_CASES, verify_sealed_bid_case
    except Exception as exc:
        return {
            "status": "inconclusive",
            "reason": "import_error",
            "signal": None,
            "counterexample": {"error": str(exc)},
            "metrics": {},
            "command": cmd,
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": str(exc)[-1200:],
        }

    rows: list[dict[str, Any]] = []
    mismatch: dict[str, Any] | None = None
    for idx, case in enumerate(SEALED_BID_CURATED_CASES, 1):
        ok, detail = verify_sealed_bid_case(case)
        row = {"case_index": int(idx), "ok": bool(ok), **detail}
        rows.append(row)
        if mismatch is None and not ok:
            mismatch = row

    signal = mismatch is None
    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": mismatch,
        "metrics": {"case_count": len(rows), "rows": rows},
        "command": cmd,
        "duration_s": float(time.time() - t0),
        "stdout_tail": "",
        "stderr_tail": "",
    }


def _check_sealed_bid_bond_surface_safe(mode: str, timeout_s: int) -> dict[str, Any]:
    del timeout_s
    t0 = time.time()
    cmd = ["internal_python_eval", "sealed_bid_bond_surface_safe"]
    try:
        import sys
        if str(ROOT) not in sys.path:
            sys.path.insert(0, str(ROOT))
        from src.core.sealed_bid_bonds import BondedSealedBidCommit, SealedBidRevealRef, settle_sealed_bid_non_reveal_bonds
        from tools.metamuse_sealed_bid_bond_lane import SEALED_BID_BOND_CURATED_CASES
    except Exception as exc:
        return {
            "status": "inconclusive",
            "reason": "import_error",
            "signal": None,
            "counterexample": {"error": str(exc)},
            "metrics": {},
            "command": cmd,
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": str(exc)[-1200:],
        }

    bad_case = None
    rows: list[dict[str, Any]] = []
    for idx, case in enumerate(SEALED_BID_BOND_CURATED_CASES, 1):
        outcome = settle_sealed_bid_non_reveal_bonds(
            commits=[BondedSealedBidCommit(c.bidder_id, c.commitment, c.bond_amount) for c in case.commits],
            reveals=[SealedBidRevealRef(bidder_id, commitment) for bidder_id, commitment in case.reveals],
        )
        no_free_non_reveal = int(outcome.total_slashed) == sum(
            int(c.bond_amount)
            for c in case.commits
            if (str(c.bidder_id), str(c.commitment)) not in set((str(b), str(cm)) for b, cm in case.reveals)
        )
        conserved = int(outcome.total_bonded) == int(outcome.total_refunded + outcome.total_slashed)
        row = {
            "case_index": int(idx),
            "no_free_non_reveal": bool(no_free_non_reveal),
            "conserved": bool(conserved),
            "total_bonded": int(outcome.total_bonded),
            "total_refunded": int(outcome.total_refunded),
            "total_slashed": int(outcome.total_slashed),
        }
        rows.append(row)
        if bad_case is None and (not no_free_non_reveal or not conserved):
            bad_case = row

    signal = bad_case is None
    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": bad_case,
        "metrics": {"case_count": len(rows), "rows": rows},
        "command": cmd,
        "duration_s": float(time.time() - t0),
        "stdout_tail": "",
        "stderr_tail": "",
    }


def _check_sealed_bid_bond_exhaustive_small(mode: str, timeout_s: int) -> dict[str, Any]:
    del timeout_s
    t0 = time.time()
    cmd = ["internal_python_eval", "sealed_bid_bond_exhaustive_small"]
    try:
        import sys
        if str(ROOT) not in sys.path:
            sys.path.insert(0, str(ROOT))
        from src.core.sealed_bid_bonds import BondedSealedBidCommit, SealedBidRevealRef, settle_sealed_bid_non_reveal_bonds
    except Exception as exc:
        return {
            "status": "inconclusive",
            "reason": "import_error",
            "signal": None,
            "counterexample": {"error": str(exc)},
            "metrics": {},
            "command": cmd,
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": str(exc)[-1200:],
        }

    checked = 0
    mismatch = None
    bidder_ids = ["a", "b", "c"]
    for commit_count in range(0, 4):
        commits = [BondedSealedBidCommit(bidder_ids[i], f"c{i}", bond_amount=((i % 3) + 1)) for i in range(commit_count)]
        max_mask = 1 << commit_count
        for mask in range(max_mask):
            reveals = [SealedBidRevealRef(bidder_ids[i], f"c{i}") for i in range(commit_count) if (mask >> i) & 1]
            outcome = settle_sealed_bid_non_reveal_bonds(commits=commits, reveals=reveals)
            checked += 1
            expected_refunded = sum(commits[i].bond_amount for i in range(commit_count) if (mask >> i) & 1)
            expected_slashed = sum(commits[i].bond_amount for i in range(commit_count) if ((mask >> i) & 1) == 0)
            if not (
                int(outcome.total_refunded) == int(expected_refunded)
                and int(outcome.total_slashed) == int(expected_slashed)
                and int(outcome.total_bonded) == int(expected_refunded + expected_slashed)
                and int(outcome.refunded_bid_count) == bin(mask).count("1")
                and int(outcome.slashed_bid_count) == int(commit_count - bin(mask).count("1"))
            ):
                mismatch = {
                    "commit_count": int(commit_count),
                    "mask": int(mask),
                    "expected_refunded": int(expected_refunded),
                    "expected_slashed": int(expected_slashed),
                    "got_refunded": int(outcome.total_refunded),
                    "got_slashed": int(outcome.total_slashed),
                    "got_total_bonded": int(outcome.total_bonded),
                }
                break
        if mismatch is not None:
            break

    signal = mismatch is None
    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": mismatch,
        "metrics": {"checked_cases": int(checked)},
        "command": cmd,
        "duration_s": float(time.time() - t0),
        "stdout_tail": "",
        "stderr_tail": "",
    }


def _check_batch_clearing_gap_exists(mode: str, timeout_s: int) -> dict[str, Any]:
    cmd = ["python3", "tools/morph_batch_clearing_miner.py", "--test", "--json"]
    cmd_res = _run_cmd(cmd, timeout_s=timeout_s)
    if cmd_res.timeout:
        return {
            "status": "inconclusive",
            "reason": "timeout",
            "signal": None,
            "counterexample": None,
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    payload = _extract_json(cmd_res.stdout)
    if not cmd_res.ok or payload is None:
        return {
            "status": "inconclusive",
            "reason": "command_error_or_unparseable_json",
            "signal": None,
            "counterexample": None,
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    known_gap = int(((payload.get("known_counterexample") or {}).get("A_gap")) or 0)
    two_intent_gap = int(((payload.get("search_results") or {}).get("2_intent_gap")) or 0)
    five_intent_gap = int(((payload.get("search_results") or {}).get("5_intent_gap")) or 0)
    signal = bool(str(payload.get("status", "")).upper() == "PASS" and max(known_gap, two_intent_gap, five_intent_gap) >= 1)
    counterexample = None
    if signal:
        counterexample = payload.get("known_counterexample")
    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": counterexample,
        "metrics": {"known_gap": known_gap, "two_intent_gap": two_intent_gap, "five_intent_gap": five_intent_gap},
        "command": cmd,
        "duration_s": cmd_res.duration_s,
        "stdout_tail": cmd_res.stdout[-1200:],
        "stderr_tail": cmd_res.stderr[-1200:],
    }


def _check_perp_lp_fee_share_guard(mode: str, timeout_s: int) -> dict[str, Any]:
    cmd = [
        "python3",
        "tools/perp_oracle_manipulation_lp_sweep.py",
        "--reserve-base",
        "100",
        "--reserve-quote",
        "200",
        "--fee-bps",
        "10",
        "--max-r",
        "100",
        "--max-pos-abs",
        "50",
        "--max-move-bps",
        "100",
        "--target-profit-quote",
        "1",
    ]
    cmd_res = _run_cmd(cmd, timeout_s=timeout_s)
    if cmd_res.timeout:
        return {
            "status": "inconclusive",
            "reason": "timeout",
            "signal": None,
            "counterexample": None,
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    payload = _extract_json(cmd_res.stdout)
    if not cmd_res.ok or payload is None:
        return {
            "status": "inconclusive",
            "reason": "command_error_or_unparseable_json",
            "signal": None,
            "counterexample": None,
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    rows = payload.get("rows")
    if not isinstance(rows, list) or not rows:
        return {
            "status": "inconclusive",
            "reason": "missing_rows",
            "signal": None,
            "counterexample": None,
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    attack_by_share: dict[int, bool] = {}
    example_by_share: dict[int, Any] = {}
    for row in rows:
        try:
            share = int(row["protocol_fee_share_bps"])
            found = bool(row["attack_found"])
        except Exception:
            continue
        attack_by_share[share] = found
        example_by_share[share] = row.get("witness")
    has_partial_attack = any(found for share, found in attack_by_share.items() if share < 10_000)
    no_full_attack = attack_by_share.get(10_000) is False
    signal = bool(has_partial_attack and no_full_attack)
    counterexample = None
    if signal:
        counterexample = {
            "partial_attack_share": min((s for s, f in attack_by_share.items() if s < 10_000 and f), default=None),
            "partial_attack_witness": example_by_share.get(
                min((s for s, f in attack_by_share.items() if s < 10_000 and f), default=-1)
            ),
            "full_capture_attack_found": attack_by_share.get(10_000),
            "full_capture_witness": example_by_share.get(10_000),
        }
    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": counterexample,
        "metrics": {"attack_found_by_fee_share_bps": attack_by_share},
        "command": cmd,
        "duration_s": cmd_res.duration_s,
        "stdout_tail": cmd_res.stdout[-1200:],
        "stderr_tail": cmd_res.stderr[-1200:],
    }


def _check_perp_reserve_hardening_effect(mode: str, timeout_s: int) -> dict[str, Any]:
    cmd = [
        "python3",
        "tools/perp_oracle_manipulation_sweep.py",
        "--reserves",
        "100,200,10000",
        "--fee-bps",
        "10,30",
        "--max-move-bps",
        "50,100",
        "--max-pos-abs",
        "50,100",
        "--max-trade-in",
        "100",
    ]
    cmd_res = _run_cmd(cmd, timeout_s=timeout_s)
    if cmd_res.timeout:
        return {
            "status": "inconclusive",
            "reason": "timeout",
            "signal": None,
            "counterexample": None,
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    payload = _extract_json(cmd_res.stdout)
    if not cmd_res.ok or payload is None:
        return {
            "status": "inconclusive",
            "reason": "command_error_or_unparseable_json",
            "signal": None,
            "counterexample": None,
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    rows = payload.get("results")
    if not isinstance(rows, list) or not rows:
        return {
            "status": "inconclusive",
            "reason": "missing_results",
            "signal": None,
            "counterexample": None,
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    best_by_reserve: dict[int, float] = {}
    for row in rows:
        try:
            reserve = int(row["reserve"])
            profit = float(row["net_profit_quote"])
        except Exception:
            continue
        cur = best_by_reserve.get(reserve)
        if cur is None or profit > cur:
            best_by_reserve[reserve] = profit
    p100 = best_by_reserve.get(100)
    p10000 = best_by_reserve.get(10_000)
    if p100 is None or p10000 is None:
        return {
            "status": "inconclusive",
            "reason": "missing_reserve_buckets",
            "signal": None,
            "counterexample": None,
            "metrics": {"best_profit_by_reserve": best_by_reserve},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    signal = bool(p10000 < p100)
    counterexample = None
    if signal:
        counterexample = {
            "best_profit_reserve_100": p100,
            "best_profit_reserve_10000": p10000,
            "improvement_quote": float(p100 - p10000),
        }
    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": counterexample,
        "metrics": {"best_profit_by_reserve": best_by_reserve},
        "command": cmd,
        "duration_s": cmd_res.duration_s,
        "stdout_tail": cmd_res.stdout[-1200:],
        "stderr_tail": cmd_res.stderr[-1200:],
    }


def _check_curve_sum_boost_exact_out_advantage(mode: str, timeout_s: int) -> dict[str, Any]:
    with tempfile.NamedTemporaryFile(mode="w", suffix=".json", delete=False, encoding="utf-8") as fh:
        out_path = Path(fh.name)
    cmd = [
        "python3",
        "tools/curve_comparison_sweep.py",
        "--grid-min",
        "1",
        "--grid-max",
        "20",
        "--grid-step",
        "2",
        "--dx",
        "1,2,5",
        "--no-quadratic",
        "--no-quartic-blend",
        "--no-quintic-blend",
        "--out",
        str(out_path),
    ]
    cmd_res = _run_cmd(cmd, timeout_s=timeout_s)
    try:
        if cmd_res.timeout:
            return {
                "status": "inconclusive",
                "reason": "timeout",
                "signal": None,
                "counterexample": None,
                "metrics": {},
                "command": cmd,
                "duration_s": cmd_res.duration_s,
                "stdout_tail": cmd_res.stdout[-1200:],
                "stderr_tail": cmd_res.stderr[-1200:],
            }
        if (not cmd_res.ok) or (not out_path.exists()):
            return {
                "status": "inconclusive",
                "reason": "command_error_or_missing_output",
                "signal": None,
                "counterexample": None,
                "metrics": {},
                "command": cmd,
                "duration_s": cmd_res.duration_s,
                "stdout_tail": cmd_res.stdout[-1200:],
                "stderr_tail": cmd_res.stderr[-1200:],
            }
        payload = json.loads(out_path.read_text(encoding="utf-8"))
    except Exception:
        return {
            "status": "inconclusive",
            "reason": "unparseable_json",
            "signal": None,
            "counterexample": None,
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    finally:
        out_path.unlink(missing_ok=True)
    balanced = (payload.get("scenarios") or {}).get("balanced") or {}
    wins = (balanced.get("wins") or {}).get("lower_in_for_same_dy") or {}
    exact_out = balanced.get("exact_out") or {}
    sum_boost_wins = int(wins.get("sum_boost", 0))
    cpmm_wins = int(wins.get("cpmm", 0))
    sum_boost_non_min_rate = float(((exact_out.get("sum_boost") or {}).get("non_minimal_rate")) or 0.0)
    cpmm_non_min_rate = float(((exact_out.get("cpmm") or {}).get("non_minimal_rate")) or 0.0)
    signal = bool(sum_boost_wins > cpmm_wins and sum_boost_non_min_rate <= cpmm_non_min_rate)
    counterexample = None
    if signal:
        counterexample = {
            "sum_boost_wins_lower_in_for_same_dy": sum_boost_wins,
            "cpmm_wins_lower_in_for_same_dy": cpmm_wins,
            "sum_boost_non_minimal_rate": sum_boost_non_min_rate,
            "cpmm_non_minimal_rate": cpmm_non_min_rate,
        }
    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": counterexample,
        "metrics": {
            "sum_boost_wins_lower_in_for_same_dy": sum_boost_wins,
            "cpmm_wins_lower_in_for_same_dy": cpmm_wins,
            "sum_boost_non_minimal_rate": sum_boost_non_min_rate,
            "cpmm_non_minimal_rate": cpmm_non_min_rate,
        },
        "command": cmd,
        "duration_s": cmd_res.duration_s,
        "stdout_tail": cmd_res.stdout[-1200:],
        "stderr_tail": cmd_res.stderr[-1200:],
    }


def _check_cpmm_overdelivery_witness(mode: str, timeout_s: int) -> dict[str, Any]:
    cmd = [
        "python3",
        "tools/morph_cpmm_overdelivery_miner.py",
        "--seed",
        "7",
        "--max-depth",
        "5",
        "--max-expanded",
        "300",
    ]
    cmd_res = _run_cmd(cmd, timeout_s=timeout_s)
    if cmd_res.timeout:
        return {
            "status": "inconclusive",
            "reason": "timeout",
            "signal": None,
            "counterexample": None,
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    if not cmd_res.ok:
        return {
            "status": "inconclusive",
            "reason": "command_error",
            "signal": None,
            "counterexample": None,
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    witness = ""
    outcome = ""
    for raw in cmd_res.stdout.splitlines():
        line = raw.strip()
        if line.startswith("witness:"):
            witness = line.split("witness:", 1)[1].strip()
        if line.startswith("outcome:"):
            outcome = line.split("outcome:", 1)[1].strip()
    signal = bool(outcome == "KernelSolved" and witness)
    counterexample = {"witness": witness, "outcome": outcome} if signal else None
    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": counterexample,
        "metrics": {"outcome": outcome, "has_witness": bool(witness)},
        "command": cmd,
        "duration_s": cmd_res.duration_s,
        "stdout_tail": cmd_res.stdout[-1200:],
        "stderr_tail": cmd_res.stderr[-1200:],
    }


def _check_intent_normal_form_tests(mode: str, timeout_s: int) -> dict[str, Any]:
    return _check_pytest_file(mode, timeout_s, "tests/core/test_intent_normal_form.py")


def _check_state_root_determinism(mode: str, timeout_s: int) -> dict[str, Any]:
    return _check_pytest_file(mode, timeout_s, "tests/state/test_state_root_determinism.py")


def _check_cpmm_ref_parity(mode: str, timeout_s: int) -> dict[str, Any]:
    return _check_pytest_file(mode, timeout_s, "tests/core/test_cpmm_ref_parity.py")


def _check_dex_v8_ref_parity(mode: str, timeout_s: int) -> dict[str, Any]:
    return _check_pytest_file(mode, timeout_s, "tests/core/test_dex_v8_ref_parity.py")


def _check_perp_v2_invariants(mode: str, timeout_s: int) -> dict[str, Any]:
    return _check_pytest_file(mode, timeout_s, "tests/core/test_perp_v2/test_invariants.py")


def _check_perp_v2_oracle_equiv(mode: str, timeout_s: int) -> dict[str, Any]:
    return _check_pytest_file(mode, timeout_s, "tests/core/test_perp_v2/test_oracle_equiv.py")


def _check_curve_selection_safety(mode: str, timeout_s: int) -> dict[str, Any]:
    return _check_pytest_file(mode, timeout_s, "tests/core/test_curve_selection.py")


def _check_split_routing_regression(mode: str, timeout_s: int) -> dict[str, Any]:
    return _check_pytest_file(mode, timeout_s, "tests/core/test_split_routing.py")


def _check_split_routing_adaptive_v4_dominates_dense24_w96(mode: str, timeout_s: int) -> dict[str, Any]:
    """
    Comparative check for split-routing exact-in policies on a fixed deterministic holdout.

    Signal definition:
    - adaptive_v4 keeps oracle match-rate at least as high as dense24_w96, and
    - adaptive_v4 reduces average policy calls by at least 30%.
    """
    t0 = time.time()
    dense_id = (
        "split_routing_tradeoff::dense24_w96::"
        "seed=20260218,n=200,match_bp=0,avg_calls_max=999999"
    )
    cand_id = (
        "split_routing_tradeoff::adaptive_v4::"
        "seed=20260218,n=200,match_bp=0,avg_calls_max=999999"
    )

    dense = _check_split_routing_tradeoff_dynamic("support", timeout_s, dense_id)
    cand = _check_split_routing_tradeoff_dynamic("support", timeout_s, cand_id)
    if dense is None or cand is None:
        return {
            "status": "inconclusive",
            "reason": "internal_check_unavailable",
            "signal": None,
            "counterexample": {"dense_check": dense_id, "candidate_check": cand_id},
            "metrics": {},
            "command": ["internal_python_eval", "split_routing_tradeoff", "comparative_adaptive_v4_vs_dense24_w96"],
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": "",
        }
    if dense.get("status") == "inconclusive" or cand.get("status") == "inconclusive":
        return {
            "status": "inconclusive",
            "reason": "subcheck_inconclusive",
            "signal": None,
            "counterexample": {
                "dense_status": dense.get("status"),
                "cand_status": cand.get("status"),
                "dense_reason": dense.get("reason"),
                "cand_reason": cand.get("reason"),
            },
            "metrics": {},
            "command": ["internal_python_eval", "split_routing_tradeoff", "comparative_adaptive_v4_vs_dense24_w96"],
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": "",
        }

    dense_m = (dense.get("metrics") or {})
    cand_m = (cand.get("metrics") or {})
    dense_match = float(dense_m.get("oracle_match_rate", 0.0))
    cand_match = float(cand_m.get("oracle_match_rate", 0.0))
    dense_calls = float(dense_m.get("avg_policy_calls", 0.0))
    cand_calls = float(cand_m.get("avg_policy_calls", 0.0))
    call_reduction = 0.0
    if dense_calls > 0.0:
        call_reduction = (dense_calls - cand_calls) / dense_calls

    signal = bool(cand_match >= dense_match and call_reduction >= 0.30)
    counterexample = None
    if not signal:
        counterexample = {
            "dense": {
                "match_rate": dense_match,
                "avg_calls": dense_calls,
                "worst_gap": dense_m.get("worst_gap"),
            },
            "candidate": {
                "match_rate": cand_match,
                "avg_calls": cand_calls,
                "worst_gap": cand_m.get("worst_gap"),
            },
            "call_reduction": call_reduction,
            "required_call_reduction": 0.30,
        }

    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": counterexample,
        "metrics": {
            "dense_check": dense_id,
            "candidate_check": cand_id,
            "dense_match_rate": dense_match,
            "candidate_match_rate": cand_match,
            "dense_avg_calls": dense_calls,
            "candidate_avg_calls": cand_calls,
            "call_reduction": call_reduction,
            "required_call_reduction": 0.30,
        },
        "command": ["internal_python_eval", "split_routing_tradeoff", "comparative_adaptive_v4_vs_dense24_w96"],
        "duration_s": float(time.time() - t0),
        "stdout_tail": "",
        "stderr_tail": "",
    }


def _check_split_routing_adaptive_v5_stress_closes_v4_gaps(mode: str, timeout_s: int) -> dict[str, Any]:
    """
    Comparative stress check for adaptive_v5 vs adaptive_v4.

    Signal definition over fixed stress distributions:
    - adaptive_v4 has at least one oracle mismatch (the stress regime is nontrivial),
    - adaptive_v5 has zero oracle mismatches,
    - adaptive_v5 has match-rate >= adaptive_v4,
    - adaptive_v5 average call overhead is <= 25%.
    """
    t0 = time.time()
    seeds = [20260219, 20260220]
    params = (
        "n=160,match_bp=0,avg_calls_max=999999,"
        "x_min=10,x_max=150,y_min=10,y_max=150,"
        "fee_min=0,fee_max=200,D_min=5000,D_max=14000"
    )

    rows: list[dict[str, Any]] = []
    for seed in seeds:
        v4_id = f"split_routing_tradeoff::adaptive_v4::seed={seed},{params}"
        v5_id = f"split_routing_tradeoff::adaptive_v5::seed={seed},{params}"
        v4 = _check_split_routing_tradeoff_dynamic("support", timeout_s, v4_id)
        v5 = _check_split_routing_tradeoff_dynamic("support", timeout_s, v5_id)
        if v4 is None or v5 is None:
            return {
                "status": "inconclusive",
                "reason": "internal_check_unavailable",
                "signal": None,
                "counterexample": {"seed": seed, "v4_check": v4_id, "v5_check": v5_id},
                "metrics": {},
                "command": ["internal_python_eval", "split_routing_tradeoff", "comparative_adaptive_v5_vs_v4_stress"],
                "duration_s": float(time.time() - t0),
                "stdout_tail": "",
                "stderr_tail": "",
            }
        if v4.get("status") == "inconclusive" or v5.get("status") == "inconclusive":
            return {
                "status": "inconclusive",
                "reason": "subcheck_inconclusive",
                "signal": None,
                "counterexample": {
                    "seed": seed,
                    "v4_status": v4.get("status"),
                    "v5_status": v5.get("status"),
                    "v4_reason": v4.get("reason"),
                    "v5_reason": v5.get("reason"),
                },
                "metrics": {},
                "command": ["internal_python_eval", "split_routing_tradeoff", "comparative_adaptive_v5_vs_v4_stress"],
                "duration_s": float(time.time() - t0),
                "stdout_tail": "",
                "stderr_tail": "",
            }
        v4_m = dict(v4.get("metrics") or {})
        v5_m = dict(v5.get("metrics") or {})
        rows.append(
            {
                "seed": int(seed),
                "v4": {
                    "match_rate": float(v4_m.get("oracle_match_rate", 0.0)),
                    "avg_calls": float(v4_m.get("avg_policy_calls", 0.0)),
                    "gap_mismatch_count": int(v4_m.get("gap_mismatch_count", 0) or 0),
                    "worst_gap": int(v4_m.get("worst_gap", 0) or 0),
                },
                "v5": {
                    "match_rate": float(v5_m.get("oracle_match_rate", 0.0)),
                    "avg_calls": float(v5_m.get("avg_policy_calls", 0.0)),
                    "gap_mismatch_count": int(v5_m.get("gap_mismatch_count", 0) or 0),
                    "worst_gap": int(v5_m.get("worst_gap", 0) or 0),
                },
            }
        )

    if not rows:
        return {
            "status": "inconclusive",
            "reason": "no_rows",
            "signal": None,
            "counterexample": {},
            "metrics": {},
            "command": ["internal_python_eval", "split_routing_tradeoff", "comparative_adaptive_v5_vs_v4_stress"],
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": "",
        }

    v4_match = sum(float(r["v4"]["match_rate"]) for r in rows) / float(len(rows))
    v5_match = sum(float(r["v5"]["match_rate"]) for r in rows) / float(len(rows))
    v4_calls = sum(float(r["v4"]["avg_calls"]) for r in rows) / float(len(rows))
    v5_calls = sum(float(r["v5"]["avg_calls"]) for r in rows) / float(len(rows))
    v4_gap_count = sum(int(r["v4"]["gap_mismatch_count"]) for r in rows)
    v5_gap_count = sum(int(r["v5"]["gap_mismatch_count"]) for r in rows)
    call_overhead = 0.0
    if v4_calls > 0.0:
        call_overhead = (v5_calls - v4_calls) / v4_calls

    signal = bool(
        v4_gap_count >= 1
        and v5_gap_count == 0
        and v5_match >= v4_match
        and call_overhead <= 0.25
    )
    counterexample = None
    if not signal:
        counterexample = {
            "per_seed": rows,
            "summary": {
                "v4_gap_count": v4_gap_count,
                "v5_gap_count": v5_gap_count,
                "v4_match_avg": v4_match,
                "v5_match_avg": v5_match,
                "v4_avg_calls": v4_calls,
                "v5_avg_calls": v5_calls,
                "call_overhead": call_overhead,
                "max_call_overhead": 0.25,
            },
        }

    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": counterexample,
        "metrics": {
            "seeds": seeds,
            "per_seed": rows,
            "v4_gap_count": v4_gap_count,
            "v5_gap_count": v5_gap_count,
            "v4_match_avg": v4_match,
            "v5_match_avg": v5_match,
            "v4_avg_calls": v4_calls,
            "v5_avg_calls": v5_calls,
            "call_overhead": call_overhead,
            "max_call_overhead": 0.25,
        },
        "command": ["internal_python_eval", "split_routing_tradeoff", "comparative_adaptive_v5_vs_v4_stress"],
        "duration_s": float(time.time() - t0),
        "stdout_tail": "",
        "stderr_tail": "",
    }


def _check_split_routing_adaptive_v6_dominates_v5_balanced(mode: str, timeout_s: int) -> dict[str, Any]:
    """
    Comparative balanced check for adaptive_v6 vs adaptive_v5.

    Signal definition:
    - v6 keeps match-rate >= v5 in each scenario,
    - v6 keeps stress scenarios at zero output-gap mismatches,
    - v6 reduces default-holdout average calls by at least 3%.
    """
    t0 = time.time()
    scenarios = [
        {
            "name": "default",
            "check_suffix": "seed=20260218,n=200,match_bp=0,avg_calls_max=999999",
            "expect_stress": False,
        },
        {
            "name": "stress_20260219",
            "check_suffix": (
                "seed=20260219,n=160,match_bp=0,avg_calls_max=999999,"
                "x_min=10,x_max=150,y_min=10,y_max=150,"
                "fee_min=0,fee_max=200,D_min=5000,D_max=14000"
            ),
            "expect_stress": True,
        },
        {
            "name": "stress_20260220",
            "check_suffix": (
                "seed=20260220,n=160,match_bp=0,avg_calls_max=999999,"
                "x_min=10,x_max=150,y_min=10,y_max=150,"
                "fee_min=0,fee_max=200,D_min=5000,D_max=14000"
            ),
            "expect_stress": True,
        },
    ]

    per_scenario: list[dict[str, Any]] = []
    for sc in scenarios:
        suffix = str(sc["check_suffix"])
        v5_id = f"split_routing_tradeoff::adaptive_v5::{suffix}"
        v6_id = f"split_routing_tradeoff::adaptive_v6::{suffix}"
        v5 = _check_split_routing_tradeoff_dynamic("support", timeout_s, v5_id)
        v6 = _check_split_routing_tradeoff_dynamic("support", timeout_s, v6_id)
        if v5 is None or v6 is None:
            return {
                "status": "inconclusive",
                "reason": "internal_check_unavailable",
                "signal": None,
                "counterexample": {"scenario": sc["name"], "v5_check": v5_id, "v6_check": v6_id},
                "metrics": {},
                "command": ["internal_python_eval", "split_routing_tradeoff", "comparative_adaptive_v6_vs_v5_balanced"],
                "duration_s": float(time.time() - t0),
                "stdout_tail": "",
                "stderr_tail": "",
            }
        if v5.get("status") == "inconclusive" or v6.get("status") == "inconclusive":
            return {
                "status": "inconclusive",
                "reason": "subcheck_inconclusive",
                "signal": None,
                "counterexample": {
                    "scenario": sc["name"],
                    "v5_status": v5.get("status"),
                    "v6_status": v6.get("status"),
                    "v5_reason": v5.get("reason"),
                    "v6_reason": v6.get("reason"),
                },
                "metrics": {},
                "command": ["internal_python_eval", "split_routing_tradeoff", "comparative_adaptive_v6_vs_v5_balanced"],
                "duration_s": float(time.time() - t0),
                "stdout_tail": "",
                "stderr_tail": "",
            }

        v5m = dict(v5.get("metrics") or {})
        v6m = dict(v6.get("metrics") or {})
        per_scenario.append(
            {
                "name": str(sc["name"]),
                "expect_stress": bool(sc["expect_stress"]),
                "v5": {
                    "match_rate": float(v5m.get("oracle_match_rate", 0.0)),
                    "avg_calls": float(v5m.get("avg_policy_calls", 0.0)),
                    "gap_mismatch_count": int(v5m.get("gap_mismatch_count", 0) or 0),
                    "worst_gap": int(v5m.get("worst_gap", 0) or 0),
                },
                "v6": {
                    "match_rate": float(v6m.get("oracle_match_rate", 0.0)),
                    "avg_calls": float(v6m.get("avg_policy_calls", 0.0)),
                    "gap_mismatch_count": int(v6m.get("gap_mismatch_count", 0) or 0),
                    "worst_gap": int(v6m.get("worst_gap", 0) or 0),
                },
            }
        )

    default_row = next((r for r in per_scenario if r["name"] == "default"), None)
    if default_row is None:
        return {
            "status": "inconclusive",
            "reason": "default_row_missing",
            "signal": None,
            "counterexample": {"per_scenario": per_scenario},
            "metrics": {},
            "command": ["internal_python_eval", "split_routing_tradeoff", "comparative_adaptive_v6_vs_v5_balanced"],
            "duration_s": float(time.time() - t0),
            "stdout_tail": "",
            "stderr_tail": "",
        }

    default_v5_calls = float(default_row["v5"]["avg_calls"])
    default_v6_calls = float(default_row["v6"]["avg_calls"])
    default_call_reduction = 0.0
    if default_v5_calls > 0.0:
        default_call_reduction = (default_v5_calls - default_v6_calls) / default_v5_calls

    per_scenario_match_ok = all(float(r["v6"]["match_rate"]) >= float(r["v5"]["match_rate"]) for r in per_scenario)
    stress_zero_gap_ok = all(
        int(r["v6"]["gap_mismatch_count"]) == 0 for r in per_scenario if bool(r["expect_stress"])
    )
    default_reduction_ok = bool(default_call_reduction >= 0.03)

    signal = bool(per_scenario_match_ok and stress_zero_gap_ok and default_reduction_ok)
    counterexample = None
    if not signal:
        counterexample = {
            "per_scenario": per_scenario,
            "default_call_reduction": default_call_reduction,
            "required_default_call_reduction": 0.03,
            "per_scenario_match_ok": per_scenario_match_ok,
            "stress_zero_gap_ok": stress_zero_gap_ok,
            "default_reduction_ok": default_reduction_ok,
        }

    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": counterexample,
        "metrics": {
            "per_scenario": per_scenario,
            "default_call_reduction": default_call_reduction,
            "required_default_call_reduction": 0.03,
            "per_scenario_match_ok": per_scenario_match_ok,
            "stress_zero_gap_ok": stress_zero_gap_ok,
            "default_reduction_ok": default_reduction_ok,
        },
        "command": ["internal_python_eval", "split_routing_tradeoff", "comparative_adaptive_v6_vs_v5_balanced"],
        "duration_s": float(time.time() - t0),
        "stdout_tail": "",
        "stderr_tail": "",
    }


def _check_batch_clearing_regression(mode: str, timeout_s: int) -> dict[str, Any]:
    return _check_pytest_file(mode, timeout_s, "tests/core/test_batch_clearing.py")


def _extract_local_mathlib_path_from_lean_mathlib_lakefile() -> tuple[Path | None, str | None]:
    lakefile = ROOT / "lean-mathlib" / "lakefile.lean"
    if not lakefile.exists():
        return None, "lean_mathlib_lakefile_missing"
    text = lakefile.read_text(encoding="utf-8", errors="replace")
    m = re.search(r'require\s+mathlib\s+from\s+"([^"]+)"', text)
    if m is None:
        return None, "unsupported_lakefile_mathlib_format"
    raw = str(m.group(1)).strip()
    if not raw:
        return None, "empty_mathlib_path"
    path = Path(raw)
    if not path.is_absolute():
        # Keep this strict: we want an explicit local install path, not a git ref.
        return None, "mathlib_path_not_absolute"
    return path, None


def _check_local_mathlib_mismatch_detected(mode: str, timeout_s: int) -> dict[str, Any]:
    del timeout_s
    mathlib_path, err = _extract_local_mathlib_path_from_lean_mathlib_lakefile()
    if err is not None or mathlib_path is None:
        return {
            "status": "inconclusive",
            "reason": err or "unknown_error",
            "signal": None,
            "counterexample": {"lakefile": "lean-mathlib/lakefile.lean"},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "",
        }

    toolchain_lean_mathlib = (ROOT / "lean-mathlib" / "lean-toolchain").read_text(encoding="utf-8", errors="replace").strip()
    toolchain_local_mathlib_path = mathlib_path / "lean-toolchain"
    toolchain_local_mathlib = (
        toolchain_local_mathlib_path.read_text(encoding="utf-8", errors="replace").strip()
        if toolchain_local_mathlib_path.exists()
        else ""
    )

    mismatch = False
    reasons: list[str] = []
    if not mathlib_path.exists():
        mismatch = True
        reasons.append("local_mathlib_path_missing")
    elif not mathlib_path.is_dir():
        mismatch = True
        reasons.append("local_mathlib_path_not_dir")
    if not toolchain_local_mathlib:
        mismatch = True
        reasons.append("local_mathlib_toolchain_missing")
    if toolchain_lean_mathlib and toolchain_local_mathlib and toolchain_lean_mathlib != toolchain_local_mathlib:
        mismatch = True
        reasons.append("toolchain_mismatch")

    return {
        "status": _mode_status(mode=mode, signal=mismatch),
        "reason": "ok",
        "signal": mismatch,
        "counterexample": None if mismatch else {"detail": "no_mismatch_detected"},
        "metrics": {
            "lean_mathlib_toolchain": toolchain_lean_mathlib,
            "local_mathlib_path": str(mathlib_path),
            "local_mathlib_toolchain": toolchain_local_mathlib,
            "mismatch_reasons": reasons,
        },
        "command": [],
        "duration_s": 0.0,
        "stdout_tail": "",
        "stderr_tail": "",
    }


def _check_local_mathlib_parametric_repeat3(mode: str, timeout_s: int) -> dict[str, Any]:
    # Keep the check ID stable for replay recipes.
    return _check_lean_repeat(mode, timeout_s, "lean-mathlib/Proofs/PiecewiseEnvelopeParametric.lean", 3)


def _scan_ui_native_popup_calls() -> list[dict[str, Any]]:
    src_root = ROOT / "tools" / "dex-ui" / "src"
    if not src_root.exists() or not src_root.is_dir():
        return []
    patt = re.compile(r"\bwindow\.(open|alert|confirm|prompt)\b|\balert\s*\(|\bconfirm\s*\(|\bprompt\s*\(")
    hits: list[dict[str, Any]] = []
    for path in sorted(src_root.rglob("*.jsx")) + sorted(src_root.rglob("*.js")):
        if not path.is_file():
            continue
        rel = str(path.relative_to(ROOT))
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except Exception:
            continue
        for lineno, line in enumerate(text.splitlines(), start=1):
            m = patt.search(line)
            if m is None:
                continue
            hits.append(
                {
                    "path": rel,
                    "line": lineno,
                    "match": m.group(0),
                    "snippet": line.strip()[:240],
                }
            )
    return hits


def _check_ui_no_native_popup_calls(mode: str, timeout_s: int) -> dict[str, Any]:
    del timeout_s
    hits = _scan_ui_native_popup_calls()
    signal = len(hits) == 0
    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": None if signal else {"hits": hits[:20], "hit_count": len(hits)},
        "metrics": {"hit_count": len(hits), "scan_root": "tools/dex-ui/src"},
        "command": [],
        "duration_s": 0.0,
        "stdout_tail": "",
        "stderr_tail": "",
    }


def _check_ui_native_popup_calls_exist(mode: str, timeout_s: int) -> dict[str, Any]:
    del timeout_s
    hits = _scan_ui_native_popup_calls()
    signal = len(hits) > 0
    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": None if signal else {"detail": "no_native_popup_calls_found"},
        "metrics": {"hit_count": len(hits), "scan_root": "tools/dex-ui/src"},
        "command": [],
        "duration_s": 0.0,
        "stdout_tail": "",
        "stderr_tail": "",
    }


def _check_ui_no_native_popup_calls_repeat3(mode: str, timeout_s: int) -> dict[str, Any]:
    del timeout_s
    run_counts: list[int] = []
    run_hits: list[list[dict[str, Any]]] = []
    for _ in range(3):
        hits = _scan_ui_native_popup_calls()
        run_counts.append(len(hits))
        run_hits.append(hits)
    signal = all(count == 0 for count in run_counts)
    counterexample = None
    if not signal:
        first_nonzero = next((i for i, c in enumerate(run_counts, start=1) if c > 0), 1)
        counterexample = {
            "run_index": first_nonzero,
            "run_counts": run_counts,
            "hits": run_hits[first_nonzero - 1][:20],
        }
    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": counterexample,
        "metrics": {"run_counts": run_counts, "scan_root": "tools/dex-ui/src"},
        "command": [],
        "duration_s": 0.0,
        "stdout_tail": "",
        "stderr_tail": "",
    }


def _check_ltlf_scheduler_goal_family(mode: str, timeout_s: int) -> dict[str, Any]:
    model_rel = "formal/ltlf/perp_epoch_scheduler_ltlf_v1.yaml"
    goals_rel = "formal/ltlf/perp_epoch_scheduler_goal_family_v1.json"
    model_path = ROOT / model_rel
    goals_path = ROOT / goals_rel
    if not model_path.exists() or not goals_path.exists():
        return {
            "status": "inconclusive",
            "reason": "missing_input_file",
            "signal": None,
            "counterexample": {"model": model_rel, "goals": goals_rel},
            "metrics": {},
            "command": [],
            "duration_s": 0.0,
            "stdout_tail": "",
            "stderr_tail": "missing LTLf model or goals file",
        }
    cmd = [
        "bash",
        "-lc",
        (
            "cd "
            + shlex.quote(str(ROOT))
            + " && PYTHONPATH=external/ESSO python3 -m ESSO ltlf-synth "
            + shlex.quote(model_rel)
            + " --goals-file "
            + shlex.quote(goals_rel)
            + " --scope reachable"
            + " --max-states 256"
            + " --max-param-combos 64"
            + " --max-bitvec-width 12"
            + " --termination explicit_end_action"
            + " --end-action end"
        ),
    ]
    cmd_res = _run_cmd(cmd, timeout_s=timeout_s)
    if cmd_res.timeout:
        return {
            "status": "inconclusive",
            "reason": "timeout",
            "signal": None,
            "counterexample": {"model": model_rel, "goals": goals_rel},
            "metrics": {},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    payload = _extract_json(cmd_res.stdout)
    if payload is None:
        return {
            "status": "inconclusive",
            "reason": "unparseable_json",
            "signal": None,
            "counterexample": {"model": model_rel, "goals": goals_rel},
            "metrics": {"returncode": cmd_res.returncode},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    ltlf_obj = payload.get("ltlf")
    if not isinstance(ltlf_obj, dict):
        return {
            "status": "inconclusive",
            "reason": "missing_ltlf_report",
            "signal": None,
            "counterexample": {"payload": payload},
            "metrics": {"returncode": cmd_res.returncode},
            "command": cmd,
            "duration_s": cmd_res.duration_s,
            "stdout_tail": cmd_res.stdout[-1200:],
            "stderr_tail": cmd_res.stderr[-1200:],
        }
    required_realizable = bool(ltlf_obj.get("required_realizable"))
    signal = bool(cmd_res.ok and payload.get("ok") is True and required_realizable)
    counterexample = None if signal else {"ltlf": ltlf_obj}
    return {
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": counterexample,
        "metrics": {
            "model": model_rel,
            "goals": goals_rel,
            "required_realizable": required_realizable,
            "active_goal_count": int(ltlf_obj.get("active_goal_count", 0)),
            "goal_count": int(ltlf_obj.get("goal_count", 0)),
            "maximal_sets": len(ltlf_obj.get("maximal_realizable_goal_sets") or []),
        },
        "command": cmd,
        "duration_s": cmd_res.duration_s,
        "stdout_tail": cmd_res.stdout[-1200:],
        "stderr_tail": cmd_res.stderr[-1200:],
    }


CHECK_DISPATCH = {
    "split_routing_gap": _check_split_routing_gap,
    "split_routing_no_gap": None,  # populated below
    "twap_staleness_effect": _check_twap_staleness_effect,
    "perp_clamp_profit": _check_perp_clamp_profit,
    "batch_greedy_invariants": _check_batch_greedy_invariants,
    "batch_clearing_gap_exists": _check_batch_clearing_gap_exists,
    "batch_clearing_no_gap": None,  # populated below
    "esso_cpmm_verify": _check_esso_cpmm_verify,
    "lean_batch_canonical": _check_lean_batch_canonical,
    "roundtrip_no_positive_profit": _check_roundtrip_no_positive_profit,
    "roundtrip_positive_profit_exists": None,  # populated below
    "lp_rounding_tests": _check_lp_rounding_tests,
    "settlement_normal_form": _check_settlement_normal_form,
    "settlement_ordering_nondeterminism_exists": None,  # populated below
    "il_insurance_vuln_presence": _check_il_insurance_vuln_presence,
    "il_insurance_status_quo_safe": None,  # populated below
    "route_exact_out_2hop_value": _check_route_exact_out_2hop_value,
    "route_exact_out_no_2hop_value": None,  # populated below
    "dgstr_exact_match": _check_dgstr_exact_match,
    "dgstr_eval_count": _check_dgstr_eval_count,
    "perp_lp_fee_share_guard": _check_perp_lp_fee_share_guard,
    "perp_lp_fee_share_irrelevant": None,  # populated below
    "perp_reserve_hardening_effect": _check_perp_reserve_hardening_effect,
    "curve_sum_boost_exact_out_advantage": _check_curve_sum_boost_exact_out_advantage,
    "cpmm_overdelivery_witness": _check_cpmm_overdelivery_witness,
    "cpmm_no_overdelivery": None,  # populated below
    "cpmm_no_overdelivery_guarded": None,  # populated below
    "intent_normal_form_tests": _check_intent_normal_form_tests,
    "intent_normal_form_regression_exists": None,  # populated below
    "state_root_determinism": _check_state_root_determinism,
    "state_root_nondeterminism_exists": None,  # populated below
    "cpmm_ref_parity": _check_cpmm_ref_parity,
    "cpmm_ref_parity_broken": None,  # populated below
    "dex_v8_ref_parity": _check_dex_v8_ref_parity,
    "dex_v8_ref_parity_broken": None,  # populated below
    "perp_v2_invariants": _check_perp_v2_invariants,
    "perp_v2_invariant_break_exists": None,  # populated below
    "perp_v2_oracle_equiv": _check_perp_v2_oracle_equiv,
    "perp_v2_oracle_divergence_exists": None,  # populated below
    "curve_selection_safety": _check_curve_selection_safety,
    "curve_selection_unsafe_exists": None,  # populated below
    "split_routing_regression": _check_split_routing_regression,
    "custom::split_routing::adaptive_v4_dominates_dense24_w96": _check_split_routing_adaptive_v4_dominates_dense24_w96,
    "custom::split_routing::adaptive_v5_stress_closes_v4_gaps": _check_split_routing_adaptive_v5_stress_closes_v4_gaps,
    "custom::split_routing::adaptive_v6_dominates_v5_balanced": _check_split_routing_adaptive_v6_dominates_v5_balanced,
    "split_routing_regression_exists": None,  # populated below
    "batch_clearing_regression": _check_batch_clearing_regression,
    "batch_clearing_invariant_break_exists": None,  # populated below
    "custom::local_mathlib::mismatch_detected": _check_local_mathlib_mismatch_detected,
    "custom::local_mathlib::parametric_repeat3": _check_local_mathlib_parametric_repeat3,
    "custom::ui::no_native_popup_calls": _check_ui_no_native_popup_calls,
    "custom::ui::native_popup_calls_exist": _check_ui_native_popup_calls_exist,
    "custom::ui::no_native_popup_calls_repeat3": _check_ui_no_native_popup_calls_repeat3,
    "ltlf_scheduler_goal_family": _check_ltlf_scheduler_goal_family,
}


def _check_split_routing_no_gap(mode: str, timeout_s: int) -> dict[str, Any]:
    base = _check_split_routing_gap("support", timeout_s)
    if base.get("status") == "inconclusive":
        base["mode"] = mode
        return base
    has_gap = bool(base.get("signal"))
    signal_no_gap = not has_gap
    return {
        **base,
        "status": _mode_status(mode=mode, signal=signal_no_gap),
        "signal": signal_no_gap,
        "counterexample": base.get("counterexample") if not signal_no_gap else None,
        "reason": "ok",
    }


def _check_roundtrip_positive_profit_exists(mode: str, timeout_s: int) -> dict[str, Any]:
    base = _check_roundtrip_no_positive_profit("support", timeout_s)
    if base.get("status") == "inconclusive":
        base["mode"] = mode
        return base
    no_positive = bool(base.get("signal"))
    positive_exists = not no_positive
    counterexample = None
    if not positive_exists:
        counterexample = {"max_profit_by_curve": (base.get("metrics") or {}).get("max_profit_by_curve", {})}
    return {
        **base,
        "status": _mode_status(mode=mode, signal=positive_exists),
        "signal": positive_exists,
        "counterexample": counterexample,
        "reason": "ok",
    }


def _check_batch_clearing_no_gap(mode: str, timeout_s: int) -> dict[str, Any]:
    base = _check_batch_clearing_gap_exists("support", timeout_s)
    if base.get("status") == "inconclusive":
        base["mode"] = mode
        return base
    has_gap = bool(base.get("signal"))
    no_gap = not has_gap
    return {
        **base,
        "status": _mode_status(mode=mode, signal=no_gap),
        "signal": no_gap,
        "counterexample": base.get("counterexample") if not no_gap else None,
        "reason": "ok",
    }


def _check_settlement_ordering_nondeterminism_exists(mode: str, timeout_s: int) -> dict[str, Any]:
    base = _check_settlement_normal_form("support", timeout_s)
    if base.get("status") == "inconclusive":
        base["mode"] = mode
        return base
    stable = bool(base.get("signal"))
    nondeterminism_exists = not stable
    counterexample = None
    if not nondeterminism_exists:
        counterexample = {"normal_form_metrics": base.get("metrics")}
    return {
        **base,
        "status": _mode_status(mode=mode, signal=nondeterminism_exists),
        "signal": nondeterminism_exists,
        "counterexample": counterexample,
        "reason": "ok",
    }


def _check_il_insurance_status_quo_safe(mode: str, timeout_s: int) -> dict[str, Any]:
    base = _check_il_insurance_vuln_presence("support", timeout_s)
    if base.get("status") == "inconclusive":
        base["mode"] = mode
        return base
    vuln_present = bool(base.get("signal"))
    status_quo_safe = not vuln_present
    counterexample = base.get("counterexample") if not status_quo_safe else None
    return {
        **base,
        "status": _mode_status(mode=mode, signal=status_quo_safe),
        "signal": status_quo_safe,
        "counterexample": counterexample,
        "reason": "ok",
    }


def _check_route_exact_out_no_2hop_value(mode: str, timeout_s: int) -> dict[str, Any]:
    base = _check_route_exact_out_2hop_value("support", timeout_s)
    if base.get("status") == "inconclusive":
        base["mode"] = mode
        return base
    has_value = bool(base.get("signal"))
    no_value = not has_value
    return {
        **base,
        "status": _mode_status(mode=mode, signal=no_value),
        "signal": no_value,
        "counterexample": base.get("counterexample") if not no_value else None,
        "reason": "ok",
    }


def _check_perp_lp_fee_share_irrelevant(mode: str, timeout_s: int) -> dict[str, Any]:
    base = _check_perp_lp_fee_share_guard("support", timeout_s)
    if base.get("status") == "inconclusive":
        base["mode"] = mode
        return base
    fee_share_guard_effective = bool(base.get("signal"))
    fee_share_irrelevant = not fee_share_guard_effective
    return {
        **base,
        "status": _mode_status(mode=mode, signal=fee_share_irrelevant),
        "signal": fee_share_irrelevant,
        "counterexample": base.get("counterexample") if not fee_share_irrelevant else None,
        "reason": "ok",
    }


def _check_cpmm_no_overdelivery(mode: str, timeout_s: int) -> dict[str, Any]:
    base = _check_cpmm_overdelivery_witness("support", timeout_s)
    if base.get("status") == "inconclusive":
        base["mode"] = mode
        return base
    has_witness = bool(base.get("signal"))
    no_witness = not has_witness
    counterexample = base.get("counterexample") if not no_witness else None
    return {
        **base,
        "status": _mode_status(mode=mode, signal=no_witness),
        "signal": no_witness,
        "counterexample": counterexample,
        "reason": "ok",
    }


def _check_cpmm_no_overdelivery_guarded(mode: str, timeout_s: int) -> dict[str, Any]:
    base = _check_cpmm_overdelivery_witness("support", timeout_s)
    if base.get("status") == "inconclusive":
        base["mode"] = mode
        return base

    cex = base.get("counterexample") or {}
    witness_raw = str(cex.get("witness", ""))
    if not witness_raw:
        return {
            **base,
            "status": "inconclusive",
            "reason": "missing_witness",
            "signal": None,
        }

    try:
        obj = json.loads(witness_raw)
        reserve_in = int(obj["reserve_in"])
        reserve_out = int(obj["reserve_out"])
        amount_out = int(obj["amount_out"])
        fee_bps = int(obj["fee_bps"])
    except Exception:
        return {
            **base,
            "status": "inconclusive",
            "reason": "unparseable_witness",
            "signal": None,
        }

    if str(ROOT) not in sys.path:
        sys.path.insert(0, str(ROOT))
    from src.core.cpmm import swap_exact_out

    blocked = False
    error_text = ""
    try:
        _ = swap_exact_out(
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            amount_out=amount_out,
            fee_bps=fee_bps,
            max_overdelivery_gap_abs=0,
        )
    except ValueError as exc:
        error_text = str(exc)
        blocked = "overdelivery gap exceeds absolute policy" in error_text

    signal = bool(blocked)
    counterexample = None
    if not signal:
        counterexample = {
            "witness": {
                "reserve_in": reserve_in,
                "reserve_out": reserve_out,
                "amount_out": amount_out,
                "fee_bps": fee_bps,
            },
            "error": error_text,
        }
    return {
        **base,
        "status": _mode_status(mode=mode, signal=signal),
        "reason": "ok",
        "signal": signal,
        "counterexample": counterexample,
        "metrics": {
            **(base.get("metrics") or {}),
            "guard": "max_overdelivery_gap_abs=0",
            "blocked": blocked,
        },
    }


def _check_intent_normal_form_regression_exists(mode: str, timeout_s: int) -> dict[str, Any]:
    base = _check_intent_normal_form_tests("support", timeout_s)
    if base.get("status") == "inconclusive":
        base["mode"] = mode
        return base
    stable = bool(base.get("signal"))
    regression_exists = not stable
    return {
        **base,
        "status": _mode_status(mode=mode, signal=regression_exists),
        "signal": regression_exists,
        "counterexample": base.get("counterexample") if not regression_exists else None,
        "reason": "ok",
    }


def _check_state_root_nondeterminism_exists(mode: str, timeout_s: int) -> dict[str, Any]:
    base = _check_state_root_determinism("support", timeout_s)
    if base.get("status") == "inconclusive":
        base["mode"] = mode
        return base
    deterministic = bool(base.get("signal"))
    nondeterministic = not deterministic
    return {
        **base,
        "status": _mode_status(mode=mode, signal=nondeterministic),
        "signal": nondeterministic,
        "counterexample": base.get("counterexample") if not nondeterministic else None,
        "reason": "ok",
    }


def _check_cpmm_ref_parity_broken(mode: str, timeout_s: int) -> dict[str, Any]:
    base = _check_cpmm_ref_parity("support", timeout_s)
    if base.get("status") == "inconclusive":
        base["mode"] = mode
        return base
    parity_holds = bool(base.get("signal"))
    parity_broken = not parity_holds
    return {
        **base,
        "status": _mode_status(mode=mode, signal=parity_broken),
        "signal": parity_broken,
        "counterexample": base.get("counterexample") if not parity_broken else None,
        "reason": "ok",
    }


def _check_dex_v8_ref_parity_broken(mode: str, timeout_s: int) -> dict[str, Any]:
    base = _check_dex_v8_ref_parity("support", timeout_s)
    if base.get("status") == "inconclusive":
        base["mode"] = mode
        return base
    parity_holds = bool(base.get("signal"))
    parity_broken = not parity_holds
    return {
        **base,
        "status": _mode_status(mode=mode, signal=parity_broken),
        "signal": parity_broken,
        "counterexample": base.get("counterexample") if not parity_broken else None,
        "reason": "ok",
    }


def _check_perp_v2_invariant_break_exists(mode: str, timeout_s: int) -> dict[str, Any]:
    base = _check_perp_v2_invariants("support", timeout_s)
    if base.get("status") == "inconclusive":
        base["mode"] = mode
        return base
    safe = bool(base.get("signal"))
    break_exists = not safe
    return {
        **base,
        "status": _mode_status(mode=mode, signal=break_exists),
        "signal": break_exists,
        "counterexample": base.get("counterexample") if not break_exists else None,
        "reason": "ok",
    }


def _check_perp_v2_oracle_divergence_exists(mode: str, timeout_s: int) -> dict[str, Any]:
    base = _check_perp_v2_oracle_equiv("support", timeout_s)
    if base.get("status") == "inconclusive":
        base["mode"] = mode
        return base
    equivalent = bool(base.get("signal"))
    divergence_exists = not equivalent
    return {
        **base,
        "status": _mode_status(mode=mode, signal=divergence_exists),
        "signal": divergence_exists,
        "counterexample": base.get("counterexample") if not divergence_exists else None,
        "reason": "ok",
    }


def _check_curve_selection_unsafe_exists(mode: str, timeout_s: int) -> dict[str, Any]:
    base = _check_curve_selection_safety("support", timeout_s)
    if base.get("status") == "inconclusive":
        base["mode"] = mode
        return base
    safe = bool(base.get("signal"))
    unsafe_exists = not safe
    return {
        **base,
        "status": _mode_status(mode=mode, signal=unsafe_exists),
        "signal": unsafe_exists,
        "counterexample": base.get("counterexample") if not unsafe_exists else None,
        "reason": "ok",
    }


def _check_split_routing_regression_exists(mode: str, timeout_s: int) -> dict[str, Any]:
    base = _check_split_routing_regression("support", timeout_s)
    if base.get("status") == "inconclusive":
        base["mode"] = mode
        return base
    stable = bool(base.get("signal"))
    regression_exists = not stable
    return {
        **base,
        "status": _mode_status(mode=mode, signal=regression_exists),
        "signal": regression_exists,
        "counterexample": base.get("counterexample") if not regression_exists else None,
        "reason": "ok",
    }


def _check_batch_clearing_invariant_break_exists(mode: str, timeout_s: int) -> dict[str, Any]:
    base = _check_batch_clearing_regression("support", timeout_s)
    if base.get("status") == "inconclusive":
        base["mode"] = mode
        return base
    stable = bool(base.get("signal"))
    break_exists = not stable
    return {
        **base,
        "status": _mode_status(mode=mode, signal=break_exists),
        "signal": break_exists,
        "counterexample": base.get("counterexample") if not break_exists else None,
        "reason": "ok",
    }


CHECK_DISPATCH["split_routing_no_gap"] = _check_split_routing_no_gap
CHECK_DISPATCH["roundtrip_positive_profit_exists"] = _check_roundtrip_positive_profit_exists
CHECK_DISPATCH["batch_clearing_no_gap"] = _check_batch_clearing_no_gap
CHECK_DISPATCH["settlement_ordering_nondeterminism_exists"] = _check_settlement_ordering_nondeterminism_exists
CHECK_DISPATCH["il_insurance_status_quo_safe"] = _check_il_insurance_status_quo_safe
CHECK_DISPATCH["route_exact_out_no_2hop_value"] = _check_route_exact_out_no_2hop_value
CHECK_DISPATCH["perp_lp_fee_share_irrelevant"] = _check_perp_lp_fee_share_irrelevant
CHECK_DISPATCH["cpmm_no_overdelivery"] = _check_cpmm_no_overdelivery
CHECK_DISPATCH["cpmm_no_overdelivery_guarded"] = _check_cpmm_no_overdelivery_guarded
CHECK_DISPATCH["intent_normal_form_regression_exists"] = _check_intent_normal_form_regression_exists
CHECK_DISPATCH["state_root_nondeterminism_exists"] = _check_state_root_nondeterminism_exists
CHECK_DISPATCH["cpmm_ref_parity_broken"] = _check_cpmm_ref_parity_broken
CHECK_DISPATCH["dex_v8_ref_parity_broken"] = _check_dex_v8_ref_parity_broken
CHECK_DISPATCH["perp_v2_invariant_break_exists"] = _check_perp_v2_invariant_break_exists
CHECK_DISPATCH["perp_v2_oracle_divergence_exists"] = _check_perp_v2_oracle_divergence_exists
CHECK_DISPATCH["curve_selection_unsafe_exists"] = _check_curve_selection_unsafe_exists
CHECK_DISPATCH["split_routing_regression_exists"] = _check_split_routing_regression_exists
CHECK_DISPATCH["batch_clearing_invariant_break_exists"] = _check_batch_clearing_invariant_break_exists
CHECK_DISPATCH["batch_mci_vs_bruteforce"] = _check_batch_mci_vs_bruteforce
CHECK_DISPATCH["batch_mci_vs_greedy"] = _check_batch_mci_vs_greedy
CHECK_DISPATCH["burn_receipt_replay_rejected"] = _check_burn_receipt_replay_rejected
CHECK_DISPATCH["burn_receipt_accounting_model"] = _check_burn_receipt_accounting_model
CHECK_DISPATCH["sealed_bid_private_state_surface_safe"] = _check_sealed_bid_private_state_surface_safe
CHECK_DISPATCH["sealed_bid_uniform_price_model"] = _check_sealed_bid_uniform_price_model
CHECK_DISPATCH["sealed_bid_bond_surface_safe"] = _check_sealed_bid_bond_surface_safe
CHECK_DISPATCH["sealed_bid_bond_exhaustive_small"] = _check_sealed_bid_bond_exhaustive_small


def _run_dynamic_check(check_id: str, mode: str, timeout_s: int) -> dict[str, Any] | None:
    dyn_perp_oracle_lp = _check_perp_oracle_lp_attack_dynamic(mode, timeout_s, check_id)
    if dyn_perp_oracle_lp is not None:
        return dyn_perp_oracle_lp

    dyn_split_case = _check_split_routing_case_dynamic(mode, timeout_s, check_id)
    if dyn_split_case is not None:
        return dyn_split_case

    dyn_split_tradeoff = _check_split_routing_tradeoff_dynamic(mode, timeout_s, check_id)
    if dyn_split_tradeoff is not None:
        return dyn_split_tradeoff

    dyn_exact_out_split_tradeoff = _check_exact_out_split_tradeoff_dynamic(mode, timeout_s, check_id)
    if dyn_exact_out_split_tradeoff is not None:
        return dyn_exact_out_split_tradeoff

    dyn_routing_case = _check_routing_split_case_dynamic(mode, timeout_s, check_id)
    if dyn_routing_case is not None:
        return dyn_routing_case

    dyn_gate_tradeoff = _check_exact_out_gate_tradeoff_dynamic(mode, timeout_s, check_id)
    if dyn_gate_tradeoff is not None:
        return dyn_gate_tradeoff

    if check_id.startswith("pytest_pass::"):
        raw = check_id.split("::", 1)[1]
        norm = _normalize_pytest_path(raw)
        if norm is None:
            return {
                "status": "inconclusive",
                "reason": "invalid_pytest_path",
                "signal": None,
                "counterexample": {"test_path": raw},
                "metrics": {},
                "command": ["pytest", "-q", raw],
                "duration_s": 0.0,
                "stdout_tail": "",
                "stderr_tail": "invalid pytest path",
            }
        return _check_pytest_file(mode, timeout_s, norm)

    if check_id.startswith("pytest_fail::"):
        raw = check_id.split("::", 1)[1]
        norm = _normalize_pytest_path(raw)
        if norm is None:
            return {
                "status": "inconclusive",
                "reason": "invalid_pytest_path",
                "signal": None,
                "counterexample": {"test_path": raw},
                "metrics": {},
                "command": ["pytest", "-q", raw],
                "duration_s": 0.0,
                "stdout_tail": "",
                "stderr_tail": "invalid pytest path",
            }
        base = _check_pytest_file("support", timeout_s, norm)
        if base.get("status") == "inconclusive":
            base["mode"] = mode
            return base
        pass_signal = bool(base.get("signal"))
        fail_signal = not pass_signal
        return {
            **base,
            "status": _mode_status(mode=mode, signal=fail_signal),
            "signal": fail_signal,
            "counterexample": base.get("counterexample") if not fail_signal else None,
            "reason": "ok",
        }

    m = re.match(r"^pytest_repeat(\d+)::(.+)$", check_id)
    if m:
        repeats = int(m.group(1))
        raw = str(m.group(2))
        return _check_pytest_repeat(mode, timeout_s, raw, repeats)

    if check_id.startswith("lean_pass::"):
        raw = check_id.split("::", 1)[1]
        return _check_lean_file(mode, timeout_s, raw)

    if check_id.startswith("lean_fail::"):
        raw = check_id.split("::", 1)[1]
        base = _check_lean_file("support", timeout_s, raw)
        if base.get("status") == "inconclusive":
            base["mode"] = mode
            return base
        pass_signal = bool(base.get("signal"))
        fail_signal = not pass_signal
        return {
            **base,
            "status": _mode_status(mode=mode, signal=fail_signal),
            "signal": fail_signal,
            "counterexample": base.get("counterexample") if not fail_signal else None,
            "reason": "ok",
        }

    m = re.match(r"^lean_repeat(\d+)::(.+)$", check_id)
    if m:
        repeats = int(m.group(1))
        raw = str(m.group(2))
        return _check_lean_repeat(mode, timeout_s, raw, repeats)

    m = re.match(r"^cegis_preflight_expect::([A-Za-z0-9_]+)::([A-Za-z0-9_,.-]+)::(\d+)::(\d+)::(\d+)::(.+)::(.+)$", check_id)
    if m:
        expected = str(m.group(1))
        solver_list = str(m.group(2))
        solver_timeout_ms = int(m.group(3))
        max_iters = int(m.group(4))
        ce_suite_max_size = int(m.group(5))
        model_yaml = str(m.group(6))
        synth_json = str(m.group(7))
        return _check_esso_synth_preflight_expect(
            mode,
            timeout_s,
            expected,
            model_yaml,
            synth_json,
            solvers=solver_list,
            solver_timeout_ms=solver_timeout_ms,
            max_iters=max_iters,
            ce_suite_max_size=ce_suite_max_size,
        )

    if check_id.startswith("esso_synth_nontrivial::"):
        raw = check_id.split("::", 1)[1]
        parts = raw.split("::")
        if len(parts) != 6:
            return {
                "status": "inconclusive",
                "reason": "bad_nontrivial_check_format",
                "signal": None,
                "counterexample": {"check_id": check_id},
                "metrics": {},
                "command": [],
                "duration_s": 0.0,
                "stdout_tail": "",
                "stderr_tail": "expected esso_synth_nontrivial::solvers::timeout_ms::model.yaml::synth.json::hole_id::predicate",
            }
        solver_list, timeout_ms_s, model_yaml, synth_json, hole_id, predicate = parts
        try:
            timeout_ms = int(timeout_ms_s)
        except Exception:
            return {
                "status": "inconclusive",
                "reason": "invalid_solver_timeout_ms",
                "signal": None,
                "counterexample": {"check_id": check_id, "timeout_ms": timeout_ms_s},
                "metrics": {},
                "command": [],
                "duration_s": 0.0,
                "stdout_tail": "",
                "stderr_tail": "invalid timeout_ms",
            }
        return _check_esso_synth_nontrivial(
            mode,
            timeout_s,
            model_yaml,
            synth_json,
            hole_id,
            predicate,
            solvers=solver_list,
            solver_timeout_ms=timeout_ms,
        )

    if check_id.startswith("esso_sygus_grammar_embedded::"):
        raw = check_id.split("::", 1)[1]
        parts = raw.split("::")
        if len(parts) != 4:
            return {
                "status": "inconclusive",
                "reason": "bad_grammar_check_format",
                "signal": None,
                "counterexample": {"check_id": check_id},
                "metrics": {},
                "command": [],
                "duration_s": 0.0,
                "stdout_tail": "",
                "stderr_tail": "expected esso_sygus_grammar_embedded::solvers::timeout_ms::model.yaml::synth.json",
            }
        solver_list, timeout_ms_s, model_yaml, synth_json = parts
        try:
            timeout_ms = int(timeout_ms_s)
        except Exception:
            return {
                "status": "inconclusive",
                "reason": "invalid_solver_timeout_ms",
                "signal": None,
                "counterexample": {"check_id": check_id, "timeout_ms": timeout_ms_s},
                "metrics": {},
                "command": [],
                "duration_s": 0.0,
                "stdout_tail": "",
                "stderr_tail": "invalid timeout_ms",
            }
        return _check_esso_sygus_grammar_embedded(
            mode,
            timeout_s,
            model_yaml,
            synth_json,
            solvers=solver_list,
            solver_timeout_ms=timeout_ms,
        )

    if check_id.startswith("esso_qsygus_terms_min::"):
        raw = check_id.split("::", 1)[1]
        parts = raw.split("::")
        if len(parts) != 5:
            return {
                "status": "inconclusive",
                "reason": "bad_qsygus_terms_format",
                "signal": None,
                "counterexample": {"check_id": check_id},
                "metrics": {},
                "command": [],
                "duration_s": 0.0,
                "stdout_tail": "",
                "stderr_tail": "expected esso_qsygus_terms_min::solvers::timeout_ms::model.yaml::synth.json::min_terms",
            }
        solver_list, timeout_ms_s, model_yaml, synth_json, min_terms_s = parts
        try:
            timeout_ms = int(timeout_ms_s)
            min_terms = int(min_terms_s)
        except Exception:
            return {
                "status": "inconclusive",
                "reason": "invalid_numeric_param",
                "signal": None,
                "counterexample": {"check_id": check_id, "timeout_ms": timeout_ms_s, "min_terms": min_terms_s},
                "metrics": {},
                "command": [],
                "duration_s": 0.0,
                "stdout_tail": "",
                "stderr_tail": "invalid timeout_ms/min_terms",
            }
        return _check_esso_qsygus_terms_min(
            mode,
            timeout_s,
            model_yaml,
            synth_json,
            min_terms=min_terms,
            solvers=solver_list,
            solver_timeout_ms=timeout_ms,
        )

    m = re.match(r"^esso_cpmm_quality_min_mean_ppm::([A-Za-z0-9_,.-]+)::(\d+)::(.+)::(.+)::(\d+)::(\d+)$", check_id)
    if m:
        solver_list = str(m.group(1))
        timeout_ms = int(m.group(2))
        model_yaml = str(m.group(3))
        synth_json = str(m.group(4))
        min_ppm = int(m.group(5))
        samples = int(m.group(6))
        return _check_esso_cpmm_quality_min_mean_ppm(
            mode,
            timeout_s,
            model_yaml,
            synth_json,
            min_mean_ppm=min_ppm,
            samples=samples,
            solvers=solver_list,
            solver_timeout_ms=timeout_ms,
        )

    m = re.match(r"^esso_d16_static_expect::([A-Za-z0-9_]+)::(.+)$", check_id)
    if m:
        expected = str(m.group(1))
        synth_json = str(m.group(2))
        return _check_esso_d16_static_expect(
            mode,
            timeout_s,
            expected,
            synth_json,
        )

    m = re.match(r"^esso_d16_regime_expect::([A-Za-z0-9_]+)::([A-Za-z0-9_,.-]+)::(\d+)::(.+)::(.+)$", check_id)
    if m:
        expected = str(m.group(1))
        solver_list = str(m.group(2))
        timeout_ms = int(m.group(3))
        model_yaml = str(m.group(4))
        synth_json = str(m.group(5))
        return _check_esso_d16_regime_expect(
            mode,
            timeout_s,
            expected,
            model_yaml,
            synth_json,
            solvers=solver_list,
            solver_timeout_ms=timeout_ms,
        )

    m = re.match(r"^esso_verify_solver_timeout::([A-Za-z0-9_,.-]+)::(\d+)::(.+)$", check_id)
    if m:
        solver_list = str(m.group(1))
        solver_timeout_ms = int(m.group(2))
        raw = str(m.group(3))
        return _check_esso_verify_kernel(
            mode,
            timeout_s,
            raw,
            solvers=solver_list,
            solver_timeout_ms=solver_timeout_ms,
        )

    m = re.match(r"^esso_synth_solver_timeout::([A-Za-z0-9_,.-]+)::(\d+)::(.+)::(.+)$", check_id)
    if m:
        solver_list = str(m.group(1))
        solver_timeout_ms = int(m.group(2))
        model_yaml = str(m.group(3))
        synth_json = str(m.group(4))
        return _check_esso_synth(
            mode,
            timeout_s,
            model_yaml,
            synth_json,
            solvers=solver_list,
            solver_timeout_ms=solver_timeout_ms,
        )

    m = re.match(r"^esso_synth_solver::([A-Za-z0-9_,.-]+)::(.+)::(.+)$", check_id)
    if m:
        solver_list = str(m.group(1))
        model_yaml = str(m.group(2))
        synth_json = str(m.group(3))
        return _check_esso_synth(
            mode,
            timeout_s,
            model_yaml,
            synth_json,
            solvers=solver_list,
        )

    m = re.match(r"^esso_synth_fail_solver_timeout::([A-Za-z0-9_,.-]+)::(\d+)::(.+)::(.+)$", check_id)
    if m:
        solver_list = str(m.group(1))
        solver_timeout_ms = int(m.group(2))
        model_yaml = str(m.group(3))
        synth_json = str(m.group(4))
        base = _check_esso_synth(
            "support",
            timeout_s,
            model_yaml,
            synth_json,
            solvers=solver_list,
            solver_timeout_ms=solver_timeout_ms,
        )
        if base.get("status") == "inconclusive":
            base["mode"] = mode
            return base
        pass_signal = bool(base.get("signal"))
        fail_signal = not pass_signal
        return {
            **base,
            "status": _mode_status(mode=mode, signal=fail_signal),
            "signal": fail_signal,
            "counterexample": base.get("counterexample") if not fail_signal else None,
            "reason": "ok",
        }

    m = re.match(r"^esso_synth_fail_solver::([A-Za-z0-9_,.-]+)::(.+)::(.+)$", check_id)
    if m:
        solver_list = str(m.group(1))
        model_yaml = str(m.group(2))
        synth_json = str(m.group(3))
        base = _check_esso_synth(
            "support",
            timeout_s,
            model_yaml,
            synth_json,
            solvers=solver_list,
        )
        if base.get("status") == "inconclusive":
            base["mode"] = mode
            return base
        pass_signal = bool(base.get("signal"))
        fail_signal = not pass_signal
        return {
            **base,
            "status": _mode_status(mode=mode, signal=fail_signal),
            "signal": fail_signal,
            "counterexample": base.get("counterexample") if not fail_signal else None,
            "reason": "ok",
        }

    if check_id.startswith("esso_synth::"):
        raw = check_id.split("::", 1)[1]
        parts = raw.split("::", 1)
        if len(parts) != 2:
            return {
                "status": "inconclusive",
                "reason": "bad_synth_check_format",
                "signal": None,
                "counterexample": {"check_id": check_id},
                "metrics": {},
                "command": [],
                "duration_s": 0.0,
                "stdout_tail": "",
                "stderr_tail": "expected esso_synth::model.yaml::synth.json",
            }
        return _check_esso_synth(mode, timeout_s, parts[0], parts[1])

    if check_id.startswith("esso_synth_fail::"):
        raw = check_id.split("::", 1)[1]
        parts = raw.split("::", 1)
        if len(parts) != 2:
            return {
                "status": "inconclusive",
                "reason": "bad_synth_check_format",
                "signal": None,
                "counterexample": {"check_id": check_id},
                "metrics": {},
                "command": [],
                "duration_s": 0.0,
                "stdout_tail": "",
                "stderr_tail": "expected esso_synth_fail::model.yaml::synth.json",
            }
        base = _check_esso_synth("support", timeout_s, parts[0], parts[1])
        if base.get("status") == "inconclusive":
            base["mode"] = mode
            return base
        pass_signal = bool(base.get("signal"))
        fail_signal = not pass_signal
        return {
            **base,
            "status": _mode_status(mode=mode, signal=fail_signal),
            "signal": fail_signal,
            "counterexample": base.get("counterexample") if not fail_signal else None,
            "reason": "ok",
        }

    m = re.match(r"^esso_spec_debug_class::([A-Za-z0-9_]+)::(.+)::(.+)$", check_id)
    if m:
        expected_class = str(m.group(1))
        model_yaml = str(m.group(2))
        synth_json = str(m.group(3))
        return _check_esso_spec_debug_class(
            mode,
            timeout_s,
            expected_class,
            model_yaml,
            synth_json,
        )

    m = re.match(r"^esso_verify_solver::([A-Za-z0-9_,.-]+)::(.+)$", check_id)
    if m:
        solver_list = str(m.group(1))
        raw = str(m.group(2))
        return _check_esso_verify_kernel(
            mode,
            timeout_s,
            raw,
            solvers=solver_list,
        )

    m = re.match(r"^esso_fail_solver_timeout::([A-Za-z0-9_,.-]+)::(\d+)::(.+)$", check_id)
    if m:
        solver_list = str(m.group(1))
        solver_timeout_ms = int(m.group(2))
        raw = str(m.group(3))
        base = _check_esso_verify_kernel(
            "support",
            timeout_s,
            raw,
            solvers=solver_list,
            solver_timeout_ms=solver_timeout_ms,
        )
        if base.get("status") == "inconclusive":
            base["mode"] = mode
            return base
        pass_signal = bool(base.get("signal"))
        fail_signal = not pass_signal
        return {
            **base,
            "status": _mode_status(mode=mode, signal=fail_signal),
            "signal": fail_signal,
            "counterexample": base.get("counterexample") if not fail_signal else None,
            "reason": "ok",
        }

    m = re.match(r"^esso_fail_solver::([A-Za-z0-9_,.-]+)::(.+)$", check_id)
    if m:
        solver_list = str(m.group(1))
        raw = str(m.group(2))
        base = _check_esso_verify_kernel(
            "support",
            timeout_s,
            raw,
            solvers=solver_list,
        )
        if base.get("status") == "inconclusive":
            base["mode"] = mode
            return base
        pass_signal = bool(base.get("signal"))
        fail_signal = not pass_signal
        return {
            **base,
            "status": _mode_status(mode=mode, signal=fail_signal),
            "signal": fail_signal,
            "counterexample": base.get("counterexample") if not fail_signal else None,
            "reason": "ok",
        }

    m = re.match(r"^esso_repeat(\d+)_solver_timeout::([A-Za-z0-9_,.-]+)::(\d+)::(.+)$", check_id)
    if m:
        repeats = int(m.group(1))
        solver_list = str(m.group(2))
        solver_timeout_ms = int(m.group(3))
        raw = str(m.group(4))
        return _check_esso_repeat(
            mode,
            timeout_s,
            raw,
            repeats,
            solvers=solver_list,
            solver_timeout_ms=solver_timeout_ms,
        )

    m = re.match(r"^esso_repeat(\d+)_solver::([A-Za-z0-9_,.-]+)::(.+)$", check_id)
    if m:
        repeats = int(m.group(1))
        solver_list = str(m.group(2))
        raw = str(m.group(3))
        return _check_esso_repeat(
            mode,
            timeout_s,
            raw,
            repeats,
            solvers=solver_list,
        )

    if check_id.startswith("esso_verify::"):
        raw = check_id.split("::", 1)[1]
        return _check_esso_verify_kernel(mode, timeout_s, raw)

    if check_id.startswith("esso_fail::"):
        raw = check_id.split("::", 1)[1]
        base = _check_esso_verify_kernel("support", timeout_s, raw)
        if base.get("status") == "inconclusive":
            base["mode"] = mode
            return base
        pass_signal = bool(base.get("signal"))
        fail_signal = not pass_signal
        return {
            **base,
            "status": _mode_status(mode=mode, signal=fail_signal),
            "signal": fail_signal,
            "counterexample": base.get("counterexample") if not fail_signal else None,
            "reason": "ok",
        }

    m = re.match(r"^esso_repeat(\d+)::(.+)$", check_id)
    if m:
        repeats = int(m.group(1))
        raw = str(m.group(2))
        return _check_esso_repeat(mode, timeout_s, raw, repeats)

    return None


def _run_check_by_id(check_id: str, mode: str, timeout_s: int) -> dict[str, Any]:
    fn = CHECK_DISPATCH.get(check_id)
    if fn is not None:
        return fn(mode, timeout_s)
    dyn = _run_dynamic_check(check_id, mode, timeout_s)
    if dyn is not None:
        return dyn
    return {
        "status": "inconclusive",
        "reason": "unknown_check_id",
        "signal": None,
        "counterexample": {"check_id": check_id},
        "metrics": {},
        "command": [],
        "duration_s": 0.0,
        "stdout_tail": "",
        "stderr_tail": f"unknown check id: {check_id}",
    }


def main() -> int:
    ap = argparse.ArgumentParser(description="Autonomous scientist check runner (deterministic)")
    ap.add_argument("--check", required=True)
    ap.add_argument("--mode", required=True, choices=("support", "refute"))
    ap.add_argument("--timeout-s", type=int, default=180)
    ap.add_argument("--json-out", type=Path, default=None)
    args = ap.parse_args()

    check_id = str(args.check)
    result = _run_check_by_id(check_id, str(args.mode), int(args.timeout_s))
    payload = {
        "schema": "zenodex/autonomous-check/v1",
        "check": check_id,
        "mode": str(args.mode),
        "timestamp_unix": int(time.time()),
        **result,
    }

    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(payload, sort_keys=True))

    st = str(payload.get("status", "error"))
    if st == "pass":
        return 0
    if st == "fail":
        return 1
    if st == "inconclusive":
        return 2
    return 3


if __name__ == "__main__":
    raise SystemExit(main())
