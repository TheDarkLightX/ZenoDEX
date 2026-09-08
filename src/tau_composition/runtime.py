"""Bounded access to separately installed Tau logical procedures.

Only generated queries enter this internal adapter. External deadlines, missing
results, parser failures and engine errors are UNKNOWN, never logical false.
No incomplete internal search cap is enabled. Tau is not redistributed.
"""

from __future__ import annotations

import hashlib
import math
import os
import re
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path

from src.integration.tau_runner import _run_subprocess_with_output_caps

_ANSI = re.compile(r"\x1b\[[0-9;]*m")
_RESULT = re.compile(r"%\d+:\s*(.*?)\s*", re.DOTALL)
_MAX_QUERY_BYTES = 256_000


class TauQueryError(RuntimeError):
    """Stable failure code; carries no satisfiability or authority verdict."""

    def __init__(self, code: str) -> None:
        self.code = code
        super().__init__(code)


@dataclass(frozen=True, slots=True)
class QueryRecord:
    operation: str
    query: str
    stdout: str
    stderr: str
    elapsed_seconds: float
    binary_sha256: str


def _digest(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def _check_generated_formula(formula: str) -> None:
    if not formula or len(formula.encode("utf-8")) > _MAX_QUERY_BYTES:
        raise TauQueryError("query_size")
    # The application generates a closed BA fragment, not arbitrary REPL code.
    if not re.fullmatch(r"[A-Za-z0-9_\s{}():,&|^'!<>=\-]+", formula):
        raise TauQueryError("query_fragment")
    if ":=" in formula or "\n" in formula or "\r" in formula:
        raise TauQueryError("query_fragment")


class TauRuntime:
    """One explicit executable and external time budget per isolated query."""

    def __init__(self, binary: str | Path, *, timeout_seconds: float = 10.0, max_queries: int = 256) -> None:
        self.binary = Path(binary).expanduser().resolve(strict=True)
        if not self.binary.is_file() or not os.access(self.binary, os.X_OK):
            raise TauQueryError("binary_not_executable")
        if type(timeout_seconds) not in (int, float):
            raise TauQueryError("timeout_domain")
        if not math.isfinite(timeout_seconds) or not 0 < timeout_seconds <= 120:
            raise TauQueryError("timeout_domain")
        self.timeout_seconds = float(timeout_seconds)
        if type(max_queries) is not int or not 1 <= max_queries <= 4096:
            raise TauQueryError("query_budget_domain")
        self.max_queries = max_queries
        self.binary_sha256 = _digest(self.binary)
        self.records: list[QueryRecord] = []

    def check_subject(self) -> None:
        if len(self.records) >= self.max_queries:
            raise TauQueryError("native_query_budget")
        if _digest(self.binary) != self.binary_sha256:
            raise TauQueryError("binary_changed")

    def _query(self, operation: str, formula: str) -> str:
        if operation not in {"lgrs", "valid", "qelim", "sat"}:
            raise TauQueryError("operation_unsupported")
        _check_generated_formula(formula)
        self.check_subject()
        query = f"{operation} {formula}"
        command = [str(self.binary), "--charvar", "false", "--severity", "error", "-e", query]
        start = time.perf_counter()
        with tempfile.TemporaryDirectory(prefix="tau-composition-") as directory:
            rc, stdout, stderr = _run_subprocess_with_output_caps(
                command, input_text="", cwd=Path(directory),
                timeout_s=self.timeout_seconds,
                max_stdout_bytes=512_000, max_stderr_bytes=32_000,
            )
        clean = _ANSI.sub("", stdout).strip()
        self.records.append(QueryRecord(
            operation, query, clean, stderr, time.perf_counter() - start, self.binary_sha256,
        ))
        if rc != 0:
            raise TauQueryError("native_timeout" if "timed out" in stderr else "native_failure")
        if re.search(r"\berror\b|\bexception\b", clean + " " + stderr, re.IGNORECASE):
            raise TauQueryError("native_error")
        if not clean:
            raise TauQueryError("native_empty")
        return clean

    def _logical_result(self, operation: str, formula: str) -> str:
        result = self._query(operation, formula)
        match = _RESULT.fullmatch(result)
        if match is None or "\n%" in result:
            raise TauQueryError("native_result_shape")
        return match.group(1).strip()

    def valid(self, formula: str) -> bool:
        result = self._logical_result("valid", formula)
        if result not in {"T", "F"}:
            raise TauQueryError("native_verdict_shape")
        return result == "T"

    def project(self, formula: str) -> str:
        result = self._logical_result("qelim", formula)
        if re.search(r"\b(?:ex|all|fex|fall)\b", result):
            raise TauQueryError("residual_quantifier")
        return result

    def lgrs(self, equation: str) -> str:
        result = self._query("lgrs", equation)
        if result == "no solution":
            raise TauQueryError("no_reproductive_solution")
        if not result.startswith("solution: {") or not result.endswith("}"):
            raise TauQueryError("native_solution_shape")
        return result
