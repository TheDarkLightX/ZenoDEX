"""Canonical-primitive cross-language differential harness.

The authoritative Python encoders live in ``src/state/canonical.py``. This
module wraps two of them — ``canonical_json_bytes`` and ``hex_to_bytes_fixed`` —
in the same per-case result shape the Rust ``canonical-hash`` CLI subcommand
emits, so a test can prove byte-for-byte agreement.

Case shapes (input):
    {"op": "json_bytes"|"json_hash", "value": <any JSON value>}
    {"op": "domain_json_hash", "label": "...", "version": <int>, "value": <any JSON value>}
    {"op": "hex_to_bytes", "hex": "0x..", "nbytes": <int>}

Result shape (output), per case, index-aligned with the input list:
    {"index": i, "ok": True,  "bytes": "0x..", "hash": "0x.."}   # json ops
    {"index": i, "ok": True,  "bytes": "0x.."}                    # hex op
    {"index": i, "ok": False, "code": "<reason>"}                 # rejection

Only ``ok`` (and, when accepted, ``bytes``/``hash``) are compared across
runtimes: Python authority raises exceptions rather than emitting machine reason
codes, so the specific reject ``code`` is asserted in the Rust unit tests, not
in the differential.
"""

from __future__ import annotations

import json
import os
import random
import shutil
import subprocess
from pathlib import Path
from typing import Any

from src.state.canonical import (
    canonical_json_bytes,
    domain_sep_bytes,
    hex_to_bytes_fixed,
    sha256_hex,
)

KERNEL = "canonical"
SCHEMA_VERSION = 1

_HERE = Path(__file__).resolve().parent
_REPO = _HERE.parents[1]
RUST_RUNTIME_DIR = _REPO / "rust-runtime"


def py_eval(index: int, case: dict) -> dict:
    """Evaluate one case through the Python authority, in the Rust result shape."""
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
            out = hex_to_bytes_fixed(
                case.get("hex"), nbytes=case.get("nbytes"), name="vector"
            )
        except (TypeError, ValueError):
            return {"index": index, "ok": False}
        return {"index": index, "ok": True, "bytes": "0x" + out.hex()}
    return {"index": index, "ok": False}


def py_eval_all(cases: list[dict]) -> list[dict]:
    return [py_eval(i, c) for i, c in enumerate(cases)]


def static_cases() -> list[dict]:
    """A deterministic corpus covering accept + reject paths for both ops."""
    return [
        # --- canonical_json_bytes: scalars ---
        {"op": "json_bytes", "value": None},
        {"op": "json_bytes", "value": True},
        {"op": "json_bytes", "value": False},
        {"op": "json_bytes", "value": 0},
        {"op": "json_bytes", "value": -123},
        {"op": "json_bytes", "value": "ab"},
        # --- key sorting + compaction + nesting ---
        {"op": "json_hash", "value": {"b": 2, "a": 1}},
        {"op": "json_bytes", "value": {"b": 2, "a": 1}},
        {"op": "json_bytes", "value": {"z": [1, "x", {"d": 4, "c": 3}], "k": True}},
        # --- big integers beyond u128 ---
        {"op": "json_bytes", "value": 10 ** 30},
        {"op": "json_hash", "value": 2 ** 130 + 7},
        # --- string escaping (quote, backslash, control, unicode) ---
        {"op": "json_bytes", "value": 'a"b\\c\n\t'},
        {"op": "json_bytes", "value": ""},
        {"op": "json_bytes", "value": "é-\U0001f600"},
        # --- a domain-shaped object (receipt-like) ---
        {
            "op": "json_hash",
            "value": {
                "module": "TauSwap",
                "version": "0.1",
                "amount": 12_345,
                "fields": {"asset": "zUSD", "min_out": 100},
            },
        },
        {
            "op": "domain_json_hash",
            "label": "zenodex.test",
            "version": 1,
            "value": {"amount": 12_345, "asset": "zUSD"},
        },
        {
            "op": "domain_json_hash",
            "label": "zenodex.test",
            "version": 2,
            "value": {"amount": 12_345, "asset": "zUSD"},
        },
        {"op": "domain_json_hash", "label": "", "version": 1, "value": {}},
        {"op": "domain_json_hash", "label": "bad\x00label", "version": 1, "value": {}},
        {"op": "domain_json_hash", "label": "é", "version": 1, "value": {}},
        {"op": "domain_json_hash", "label": "x", "version": 0, "value": {}},
        # --- canonical_json_bytes rejections ---
        {"op": "json_bytes", "value": 1.5},
        {"op": "json_bytes", "value": [1, 2.0, 3]},
        {"op": "json_bytes", "value": {"k": 0.1}},
        # --- hex_to_bytes: accept ---
        {"op": "hex_to_bytes", "hex": "0x00", "nbytes": 1},
        {"op": "hex_to_bytes", "hex": "0xff", "nbytes": 1},
        {"op": "hex_to_bytes", "hex": "0xDeAdBeEf", "nbytes": 4},
        {"op": "hex_to_bytes", "hex": "0x" + "ab" * 32, "nbytes": 32},
        {"op": "hex_to_bytes", "hex": "0x" + "cd" * 48, "nbytes": 48},
        # --- hex_to_bytes: reject ---
        {"op": "hex_to_bytes", "hex": "00", "nbytes": 1},
        {"op": "hex_to_bytes", "hex": "0x0102", "nbytes": 1},
        {"op": "hex_to_bytes", "hex": "0x01", "nbytes": 2},
        {"op": "hex_to_bytes", "hex": "0xzz", "nbytes": 1},
        {"op": "hex_to_bytes", "hex": "0x", "nbytes": 1},
    ]


# --- randomized corpus --------------------------------------------------------

_STRING_ALPHABET = "abc \"\\\n\téü\U0001f600{}[]:,0"


def _rand_string(rng: random.Random) -> str:
    return "".join(rng.choice(_STRING_ALPHABET) for _ in range(rng.randint(0, 6)))


def _rand_json(rng: random.Random, depth: int) -> Any:
    pick = rng.random()
    if depth <= 0 or pick < 0.45:
        leaf = rng.random()
        if leaf < 0.25:
            return rng.choice([None, True, False])
        if leaf < 0.7:
            # Integers, including > u128 and negatives.
            mag = rng.choice([8, 64, 128, 200])
            n = rng.randrange(0, 1 << mag)
            return -n if rng.random() < 0.3 else n
        return _rand_string(rng)
    if pick < 0.72:
        return [_rand_json(rng, depth - 1) for _ in range(rng.randint(0, 4))]
    return {
        _rand_string(rng) or f"k{i}": _rand_json(rng, depth - 1)
        for i in range(rng.randint(0, 4))
    }


def random_cases(seed: int, n: int) -> list[dict]:
    rng = random.Random(seed)
    cases: list[dict] = []
    for _ in range(n):
        roll = rng.random()
        if roll < 0.55:
            op = "json_hash" if rng.random() < 0.5 else "json_bytes"
            cases.append({"op": op, "value": _rand_json(rng, depth=3)})
        elif roll < 0.68:
            label_roll = rng.random()
            if label_roll < 0.75:
                label = rng.choice(["zenodex.test", "fee_receipt", "state_root", "x"])
            elif label_roll < 0.9:
                label = ""
            else:
                label = rng.choice(["bad\x00label", "é"])
            version = rng.choice([1, 2, 3, 0, -1])
            cases.append(
                {
                    "op": "domain_json_hash",
                    "label": label,
                    "version": version,
                    "value": _rand_json(rng, depth=2),
                }
            )
        elif roll < 0.78:
            # Occasionally inject a float to exercise reject agreement.
            cases.append({"op": "json_bytes", "value": rng.uniform(-5, 5)})
        else:
            nbytes = rng.choice([1, 2, 4, 32, 48])
            good = rng.random() < 0.6
            length = (2 * nbytes) if good else 2 * rng.choice([nbytes - 1, nbytes + 1, nbytes])
            length = max(length, 0)
            body = "".join(rng.choice("0123456789abcdefABCDEF") for _ in range(length))
            if not good and rng.random() < 0.4 and body:
                body = "z" + body[1:]
            prefix = "0x" if rng.random() < 0.85 else ""
            cases.append({"op": "hex_to_bytes", "hex": prefix + body, "nbytes": nbytes})
    return cases


# --- Rust bridge --------------------------------------------------------------


class CanonicalShadowError(RuntimeError):
    pass


def locate_or_build_cli(*, allow_build: bool = True) -> Path:
    env_bin = os.environ.get("ZENODEX_RUNTIME_BIN")
    if env_bin:
        p = Path(env_bin)
        if not p.is_file():
            raise CanonicalShadowError(f"ZENODEX_RUNTIME_BIN missing: {p}")
        return p
    if not allow_build:
        for profile in ("release", "debug"):
            candidate = RUST_RUNTIME_DIR / "target" / profile / "zenodex-runtime"
            if candidate.is_file():
                return candidate
        raise CanonicalShadowError("no prebuilt zenodex-runtime binary and --no-build set")
    if shutil.which("cargo") is None:
        raise CanonicalShadowError("cargo not found on PATH")
    build = subprocess.run(
        ["cargo", "build", "--quiet", "--bin", "zenodex-runtime"],
        cwd=str(RUST_RUNTIME_DIR),
        capture_output=True,
        text=True,
    )
    if build.returncode != 0:
        raise CanonicalShadowError(f"cargo build failed:\n{build.stderr}")
    candidate = RUST_RUNTIME_DIR / "target" / "debug" / "zenodex-runtime"
    if not candidate.is_file():
        raise CanonicalShadowError("cargo build succeeded but binary missing")
    return candidate


def run_rust(bin_path: Path, cases: list[dict]) -> list[dict]:
    """Run the ``canonical-hash`` subcommand over ``cases`` and return results."""
    request = json.dumps({"cases": cases})
    proc = subprocess.run(
        [str(bin_path), "canonical-hash", "-"],
        input=request,
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        raise CanonicalShadowError(f"rust canonical-hash exited {proc.returncode}:\n{proc.stderr}")
    out = json.loads(proc.stdout)
    return out["results"]


def diff_results(py: list[dict], rs: list[dict]) -> list[str]:
    """Return human-readable mismatches; empty list means agreement."""
    problems: list[str] = []
    if len(py) != len(rs):
        return [f"length mismatch: python {len(py)} vs rust {len(rs)}"]
    for i, (p, r) in enumerate(zip(py, rs)):
        if bool(p["ok"]) != bool(r["ok"]):
            problems.append(f"case {i}: ok python={p['ok']} rust={r['ok']}")
            continue
        if p["ok"]:
            if p.get("bytes") != r.get("bytes"):
                problems.append(
                    f"case {i}: bytes python={p.get('bytes')} rust={r.get('bytes')}"
                )
            if p.get("hash") != r.get("hash"):
                problems.append(
                    f"case {i}: hash python={p.get('hash')} rust={r.get('hash')}"
                )
    return problems
