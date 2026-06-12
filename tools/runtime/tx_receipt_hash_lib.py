"""Tx-envelope / receipt hash cross-language differential harness (Phase F).

Two authoritative hashes share one shape — `sha256(domain_sep(label, version) +
canonical_json_bytes(value))`:

  * DEX intent auth message — `src/core/dex_intent_auth_message.py`
    (`label = f"dex_intent_sig:{chain_id}"`, version 1; chain_id binds via the
    domain-sep *label*, not the JSON);
  * buyback burn-receipt body — `src/core/burn_receipts.py`
    (`label = "zenodex.burn_receipt/v1"`, version 1).

The Rust shadow exposes this as the `domain_json_hash` op of the `canonical-hash`
CLI subcommand. This harness drives the *real* authority functions and the Rust
op, proving byte-for-byte hash agreement. Scope: the hash of an already-built
canonical dict. The intent shape-gate (`dex_intent_auth_shape_gate`) and BLS
signature verification are separate, larger surfaces and out of scope here.
"""

from __future__ import annotations

import json
import os
import random
import shutil
import subprocess
from pathlib import Path

from src.core.burn_receipts import burn_receipt_hash
from src.core.dex_intent_auth_message import (
    build_dex_intent_signing_dict_v1,
    hash_dex_intent_auth_message_v1,
)

KERNEL = "tx_receipt_hash"
BURN_LABEL = "zenodex.burn_receipt/v1"

_HERE = Path(__file__).resolve().parent
_REPO = _HERE.parents[1]
RUST_RUNTIME_DIR = _REPO / "rust-runtime"


# --- case construction --------------------------------------------------------


def intent_case(intent: dict, chain_id: str) -> dict:
    """Return a Rust `domain_json_hash` case plus the authoritative Python hash."""
    signing_dict = build_dex_intent_signing_dict_v1(intent)
    py_hash = "0x" + hash_dex_intent_auth_message_v1(intent, chain_id=chain_id).hex()
    rust_case = {
        "op": "domain_json_hash",
        "label": f"dex_intent_sig:{chain_id}",
        "version": 1,
        "value": signing_dict,
    }
    return {"rust": rust_case, "py_hash": py_hash}


def burn_case(body: dict) -> dict:
    py_hash = burn_receipt_hash(body)
    rust_case = {
        "op": "domain_json_hash",
        "label": BURN_LABEL,
        "version": 1,
        "value": body,
    }
    return {"rust": rust_case, "py_hash": py_hash}


def _intent(chain="zeno-testnet-1", **over) -> dict:
    base = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "swap",
        "intent_id": "0x" + "ab" * 16,
        "sender_pubkey": "0x" + "11" * 48,
        "deadline": 100,
        "fields": {"asset_in": "zUSD", "asset_out": "zDEX", "amount_in": 1000, "min_out": 5},
    }
    base.update(over)
    return base


def static_cases() -> list[dict]:
    cases = [
        intent_case(_intent(), "zeno-testnet-1"),
        # Same intent, different chain_id -> different hash (label binding).
        intent_case(_intent(), "zeno-mainnet"),
        # With salt.
        intent_case(_intent(salt="0x" + "cd" * 16), "zeno-testnet-1"),
        # Unicode + nested fields.
        intent_case(_intent(fields={"memo": "héllo", "nested": {"b": 2, "a": 1}, "flag": True}),
                    "zeno-testnet-1"),
        # Burn receipt bodies.
        burn_case({"schema": "zenodex/burn_receipt/v1", "amount": 123, "epoch": 7}),
        burn_case({"schema": "zenodex/burn_receipt/v1", "amount": 0, "nullifier": "0x" + "00" * 32}),
        burn_case({"schema": "zenodex/burn_receipt/v1", "amount": 10 ** 30, "note": ""}),
    ]
    return cases


def random_cases(seed: int, n: int) -> list[dict]:
    rng = random.Random(seed)
    out: list[dict] = []

    def rand_scalar():
        r = rng.random()
        if r < 0.3:
            return rng.randrange(0, 1 << rng.choice([8, 64, 128]))
        if r < 0.5:
            return rng.choice([True, False, None])
        return "".join(rng.choice("abcé09 _-") for _ in range(rng.randint(0, 6)))

    def rand_fields():
        return {f"k{i}": rand_scalar() for i in range(rng.randint(0, 4))}

    for _ in range(n):
        if rng.random() < 0.6:
            chain = rng.choice(["zeno-testnet-1", "zeno-mainnet", "local"])
            intent = _intent(chain, deadline=rng.randint(0, 10**9), fields=rand_fields())
            if rng.random() < 0.4:
                intent["salt"] = "0x" + "".join(rng.choice("0123456789abcdef") for _ in range(32))
            out.append(intent_case(intent, chain))
        else:
            body = {"schema": "zenodex/burn_receipt/v1", **rand_fields(),
                    "amount": rng.randrange(0, 1 << rng.choice([8, 64, 128]))}
            out.append(burn_case(body))
    return out


# --- Rust bridge --------------------------------------------------------------


class TxHashShadowError(RuntimeError):
    pass


def locate_or_build_cli(*, allow_build: bool = True) -> Path:
    env_bin = os.environ.get("ZENODEX_RUNTIME_BIN")
    if env_bin:
        p = Path(env_bin)
        if not p.is_file():
            raise TxHashShadowError(f"ZENODEX_RUNTIME_BIN missing: {p}")
        return p
    if not allow_build:
        for profile in ("release", "debug"):
            candidate = RUST_RUNTIME_DIR / "target" / profile / "zenodex-runtime"
            if candidate.is_file():
                return candidate
        raise TxHashShadowError("no prebuilt zenodex-runtime binary and --no-build set")
    if shutil.which("cargo") is None:
        raise TxHashShadowError("cargo not found on PATH")
    build = subprocess.run(
        ["cargo", "build", "--quiet", "--bin", "zenodex-runtime"],
        cwd=str(RUST_RUNTIME_DIR),
        capture_output=True,
        text=True,
    )
    if build.returncode != 0:
        raise TxHashShadowError(f"cargo build failed:\n{build.stderr}")
    candidate = RUST_RUNTIME_DIR / "target" / "debug" / "zenodex-runtime"
    if not candidate.is_file():
        raise TxHashShadowError("cargo build succeeded but binary missing")
    return candidate


def run_rust(bin_path: Path, rust_cases: list[dict]) -> list[dict]:
    request = json.dumps({"cases": rust_cases})
    proc = subprocess.run(
        [str(bin_path), "canonical-hash", "-"],
        input=request,
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        raise TxHashShadowError(f"rust canonical-hash exited {proc.returncode}:\n{proc.stderr}")
    return json.loads(proc.stdout)["results"]


def diff_cases(cases: list[dict], rust_results: list[dict]) -> list[str]:
    problems: list[str] = []
    if len(cases) != len(rust_results):
        return [f"length mismatch: {len(cases)} vs {len(rust_results)}"]
    for i, (c, r) in enumerate(zip(cases, rust_results)):
        if not r.get("ok"):
            problems.append(f"case {i}: rust rejected ({r.get('code')})")
            continue
        if r.get("hash") != c["py_hash"]:
            problems.append(f"case {i}: hash python={c['py_hash']} rust={r.get('hash')}")
    return problems
