"""Authority-routed canonical primitive evaluation.

The low-level encoders in :mod:`src.state.canonical` remain pure Python
functions. This module is the explicit promotion boundary for the canonical
surface: callers that want deployment-profile-controlled Rust authority use this
facade, which runs the Rust canonical CLI as authority and Python as shadow when
the active profile requests it.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
from pathlib import Path
from typing import Any, Mapping

from src.state.canonical import canonical_json_bytes, domain_sep_bytes, hex_to_bytes_fixed, sha256_hex

from .authority import AuthorityDecision, AuthorityMode, AuthorityPolicy, RustUnavailable, decide, load_authority_policy


CANONICAL_SURFACE = "canonical"
RUNTIME_REQUEST_SCHEMA_VERSION = 1

_REPO = Path(__file__).resolve().parents[2]
_RUST_RUNTIME_DIR = _REPO / "rust-runtime"
_DEFAULT_TIMEOUT_SECONDS = 10.0


class CanonicalAuthorityError(RuntimeError):
    """Raised for malformed canonical authority bridge output."""


def _require_exact_fields(value: Mapping[str, Any], expected: set[str], label: str) -> None:
    actual = set(value)
    if actual == expected:
        return
    missing = sorted(expected - actual)
    extra = sorted(actual - expected)
    raise CanonicalAuthorityError(f"{label}: unexpected fields missing={missing!r} extra={extra!r}")


def _py_case(index: int, case: Mapping[str, Any]) -> dict[str, Any]:
    op = case.get("op")
    if op in ("json_bytes", "json_hash"):
        try:
            raw = canonical_json_bytes(case.get("value"))
        except (TypeError, ValueError):
            return {"index": index, "ok": False}
        return {
            "index": index,
            "ok": True,
            "bytes": "0x" + raw.hex(),
            "hash": sha256_hex(raw),
        }
    if op == "domain_json_hash":
        try:
            label = case.get("label")
            version = case.get("version", 1)
            msg = domain_sep_bytes(label, version) + canonical_json_bytes(case.get("value"))
        except (TypeError, ValueError):
            return {"index": index, "ok": False}
        return {"index": index, "ok": True, "hash": sha256_hex(msg)}
    if op == "hex_to_bytes":
        try:
            out = hex_to_bytes_fixed(case.get("hex"), nbytes=case.get("nbytes"), name="vector")
        except (TypeError, ValueError):
            return {"index": index, "ok": False}
        return {"index": index, "ok": True, "bytes": "0x" + out.hex()}
    return {"index": index, "ok": False}


def py_eval_cases(cases: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Evaluate canonical cases through the Python authority."""

    return [_py_case(i, c) for i, c in enumerate(cases)]


def diff_results(left: list[dict[str, Any]], right: list[dict[str, Any]]) -> list[str]:
    """Return result mismatches. Empty means authority-compatible agreement."""

    if len(left) != len(right):
        return [f"length mismatch: left {len(left)} vs right {len(right)}"]
    problems: list[str] = []
    for index, (a, b) in enumerate(zip(left, right)):
        if a.get("index") != index or b.get("index") != index:
            problems.append(f"case {index}: index left={a.get('index')} right={b.get('index')}")
            continue
        if not isinstance(a.get("ok"), bool) or not isinstance(b.get("ok"), bool):
            problems.append(f"case {index}: malformed ok left={a.get('ok')} right={b.get('ok')}")
            continue
        if a.get("ok") != b.get("ok"):
            problems.append(f"case {index}: ok left={a.get('ok')} right={b.get('ok')}")
            continue
        if a.get("ok"):
            if a.get("bytes") != b.get("bytes"):
                problems.append(f"case {index}: bytes left={a.get('bytes')} right={b.get('bytes')}")
            if a.get("hash") != b.get("hash"):
                problems.append(f"case {index}: hash left={a.get('hash')} right={b.get('hash')}")
    return problems


def _expected_rust_success_fields(case: Mapping[str, Any]) -> set[str]:
    op = case.get("op")
    if op in {"json_bytes", "json_hash"}:
        return {"index", "ok", "bytes", "hash"}
    if op == "domain_json_hash":
        return {"index", "ok", "hash"}
    if op == "hex_to_bytes":
        return {"index", "ok", "bytes"}
    raise CanonicalAuthorityError(f"rust canonical success for unsupported op {op!r}")


def _validate_rust_results(cases: list[dict[str, Any]], results: list[Any]) -> list[dict[str, Any]]:
    if len(results) != len(cases):
        raise CanonicalAuthorityError(
            f"rust canonical-hash result length mismatch: {len(results)} vs {len(cases)}"
        )
    out: list[dict[str, Any]] = []
    for index, (case, result) in enumerate(zip(cases, results, strict=True)):
        if not isinstance(result, dict):
            raise CanonicalAuthorityError(f"rust canonical-hash result {index} must be an object")
        ok = result.get("ok")
        if ok is True:
            _require_exact_fields(result, _expected_rust_success_fields(case), f"rust canonical result {index}")
        elif ok is False:
            _require_exact_fields(result, {"index", "ok", "code"}, f"rust canonical result {index}")
        else:
            raise CanonicalAuthorityError(f"rust canonical result {index} ok must be a bool")
        if result.get("index") != index:
            raise CanonicalAuthorityError(f"rust canonical result {index} index mismatch")
        out.append(result)
    return out


def locate_runtime_binary(*, allow_build: bool = False) -> Path:
    """Locate the Rust runtime CLI.

    Production/testnet deployments should set ``ZENODEX_RUNTIME_BIN`` to a
    packaged binary. Local tests may pass ``allow_build=True``.
    """

    env_bin = os.environ.get("ZENODEX_RUNTIME_BIN")
    if env_bin:
        path = Path(env_bin)
        if path.is_file():
            return path
        raise RustUnavailable(f"ZENODEX_RUNTIME_BIN missing: {path}")
    for profile in ("release", "debug"):
        candidate = _RUST_RUNTIME_DIR / "target" / profile / "zenodex-runtime"
        if candidate.is_file():
            return candidate
    if not allow_build:
        raise RustUnavailable("zenodex-runtime binary unavailable")
    if shutil.which("cargo") is None:
        raise RustUnavailable("cargo unavailable")
    build = subprocess.run(
        ["cargo", "build", "--quiet", "--bin", "zenodex-runtime"],
        cwd=str(_RUST_RUNTIME_DIR),
        capture_output=True,
        text=True,
        timeout=120,
    )
    if build.returncode != 0:
        raise RustUnavailable(f"cargo build failed: {build.stderr}")
    candidate = _RUST_RUNTIME_DIR / "target" / "debug" / "zenodex-runtime"
    if not candidate.is_file():
        raise RustUnavailable("cargo build succeeded but zenodex-runtime is missing")
    return candidate


def rust_eval_cases(
    cases: list[dict[str, Any]],
    *,
    rust_bin: Path | None = None,
    allow_build: bool = False,
    timeout_seconds: float = _DEFAULT_TIMEOUT_SECONDS,
) -> list[dict[str, Any]]:
    """Evaluate canonical cases through the Rust runtime CLI."""

    bin_path = rust_bin or locate_runtime_binary(allow_build=allow_build)
    request = json.dumps({"version": RUNTIME_REQUEST_SCHEMA_VERSION, "cases": cases})
    proc = subprocess.run(
        [str(bin_path), "canonical-hash", "-"],
        input=request,
        capture_output=True,
        text=True,
        timeout=timeout_seconds,
    )
    if proc.returncode != 0:
        raise CanonicalAuthorityError(f"rust canonical-hash exited {proc.returncode}: {proc.stderr}")
    try:
        payload = json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        raise CanonicalAuthorityError("rust canonical-hash emitted malformed JSON") from exc
    if not isinstance(payload, dict):
        raise CanonicalAuthorityError("rust canonical-hash output must be an object")
    _require_exact_fields(payload, {"version", "results"}, "rust canonical output")
    if payload.get("version") != RUNTIME_REQUEST_SCHEMA_VERSION:
        raise CanonicalAuthorityError("rust canonical-hash emitted unsupported schema version")
    results = payload.get("results")
    if not isinstance(results, list):
        raise CanonicalAuthorityError("rust canonical-hash output missing results list")
    return _validate_rust_results(cases, results)


def decide_canonical_cases(
    cases: list[dict[str, Any]],
    *,
    profile: Mapping[str, Any] | None = None,
    policy: AuthorityPolicy | None = None,
    mode: AuthorityMode | str | None = None,
    rust_bin: Path | None = None,
    allow_build: bool = False,
) -> AuthorityDecision:
    """Evaluate a canonical batch under the requested authority mode."""

    if mode is None:
        active_policy = policy if policy is not None else load_authority_policy(profile)
        mode = active_policy.mode_for(CANONICAL_SURFACE)

    return decide(
        CANONICAL_SURFACE,
        mode,
        python_fn=lambda: py_eval_cases(cases),
        rust_fn=lambda: rust_eval_cases(cases, rust_bin=rust_bin, allow_build=allow_build),
        compare=lambda py, ru: not diff_results(py, ru),
    )


def canonical_json_hash_with_authority(
    value: Any,
    *,
    profile: Mapping[str, Any] | None = None,
    policy: AuthorityPolicy | None = None,
    mode: AuthorityMode | str | None = None,
    rust_bin: Path | None = None,
    allow_build: bool = False,
) -> tuple[str, dict[str, Any]]:
    """Return ``sha256(canonical_json_bytes(value))`` plus authority metadata."""

    decision = decide_canonical_cases(
        [{"op": "json_hash", "value": value}],
        profile=profile,
        policy=policy,
        mode=mode,
        rust_bin=rust_bin,
        allow_build=allow_build,
    )
    result = decision.result[0]
    if not result.get("ok") or not isinstance(result.get("hash"), str):
        raise CanonicalAuthorityError("canonical JSON hash was rejected")
    return result["hash"], decision.metadata()
