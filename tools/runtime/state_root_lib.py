"""State-root cross-language differential harness.

The authority is `compute_state_root` in `src/state/state_root.py`. This module
builds the real domain objects (BalanceTable / pools / LPTable / NonceTable)
from a plain-JSON state description, computes the authoritative root, and shapes
the result like the Rust `verify-state-root` CLI subcommand so a test can prove
byte-for-byte agreement.

State JSON shape (all hex lowercase, 0x-prefixed; pubkey 48 bytes, asset/pool 32):

    {
      "balances":        [{"pubkey","asset","amount"}],
      "pools":           [{"pool_id","asset0","asset1","reserve0","reserve1",
                           "fee_bps","lp_supply","status","created_at",
                           "curve_tag","curve_params"}],
      "lp_balances":     [{"pubkey","pool_id","amount"}],
      "lp_duration_risk":[{"pubkey","pool_id","last_mint_timestamp",
                           "last_remove_timestamp","churn_tier",
                           "last_churn_update_timestamp"}],
      "nonces":          [{"pubkey","last_nonce"}],
      "fee_accumulator": {"dust"}
    }

Modelling rules the generator must honour (so the Python table model and the
Rust JSON view describe the *same* state):
  * sparse tables drop zero amounts — balances / lp_balances / nonces use >= 1;
  * lp_duration_risk entries must be "present" (a timestamp set or churn_tier>0),
    matching `get_all_duration_risk_metadata`'s filter;
  * pools key == pool.pool_id; pool IDs bind assets/fee/curve parameters;
  * asset0 is ordered before asset1 in canonical byte order.
"""

from __future__ import annotations

import json
import os
import random
import shutil
import subprocess
from pathlib import Path

from src.core.fees import FeeAccumulatorState
from src.state.balances import BalanceTable
from src.state.lp import LPTable
from src.state.nonces import NonceTable
from src.state.pools import PoolState, PoolStatus, compute_pool_id
from src.state.state_root import compute_state_root

KERNEL = "state_root"

_HERE = Path(__file__).resolve().parent
_REPO = _HERE.parents[1]
RUST_RUNTIME_DIR = _REPO / "rust-runtime"

_STATUS = {
    "active": PoolStatus.ACTIVE,
    "frozen": PoolStatus.FROZEN,
    "disabled": PoolStatus.DISABLED,
}
_STATUS_LABEL = {v: k for k, v in _STATUS.items()}


def build_tables(state: dict):
    """Build (balances, pools, lp, nonces, fee_accumulator) from JSON `state`.

    May raise (TypeError/ValueError) when the state is invalid — e.g. a CPMM pool
    with non-empty curve_params, an out-of-range nonce, or a bad pubkey.
    """
    balances = BalanceTable()
    for e in state.get("balances", []) or []:
        balances.set(e["pubkey"], e["asset"], e["amount"])

    pools: dict[str, PoolState] = {}
    for e in state.get("pools", []) or []:
        status = _STATUS.get(e["status"])
        if status is None:
            raise ValueError(f"unknown pool status: {e['status']!r}")
        pools[e["pool_id"]] = PoolState(
            pool_id=e["pool_id"],
            asset0=e["asset0"],
            asset1=e["asset1"],
            reserve0=e["reserve0"],
            reserve1=e["reserve1"],
            fee_bps=e["fee_bps"],
            lp_supply=e["lp_supply"],
            status=status,
            created_at=e["created_at"],
            curve_tag=e.get("curve_tag", "CPMM"),
            curve_params=e.get("curve_params", ""),
        )

    lp = LPTable()
    for e in state.get("lp_balances", []) or []:
        lp.set(e["pubkey"], e["pool_id"], e["amount"])
    for e in state.get("lp_duration_risk", []) or []:
        pk, pool = e["pubkey"], e["pool_id"]
        if e.get("last_mint_timestamp") is not None:
            lp.set_last_mint_timestamp(pk, pool, e["last_mint_timestamp"])
        if e.get("last_remove_timestamp") is not None:
            lp.set_last_remove_timestamp(pk, pool, e["last_remove_timestamp"])
        if e.get("churn_tier", 0):
            lp.set_churn_tier(pk, pool, e["churn_tier"])
        if e.get("last_churn_update_timestamp") is not None:
            lp.set_last_churn_update_timestamp(pk, pool, e["last_churn_update_timestamp"])

    nonces = NonceTable()
    for e in state.get("nonces", []) or []:
        nonces.set_last(e["pubkey"], e["last_nonce"])

    fee_obj = state.get("fee_accumulator")
    if fee_obj is None:
        fee_obj = {}
    if not isinstance(fee_obj, dict):
        raise TypeError("fee_accumulator must be an object")
    fee_accumulator = FeeAccumulatorState(dust=fee_obj.get("dust", 0))

    return balances, pools, lp, nonces, fee_accumulator


def state_root_from_json(state: dict) -> str:
    """Build the domain objects from `state` and return the authoritative root."""
    balances, pools, lp, nonces, fee_accumulator = build_tables(state)
    return compute_state_root(
        balances=balances,
        pools=pools,
        lp_balances=lp,
        nonces=nonces,
        fee_accumulator=fee_accumulator,
    )


def to_rust_json(state: dict) -> dict:
    """Serialize the *built* Python state back to JSON for the Rust shadow.

    This reads the actual table contents after construction, so the Rust view
    reflects every authority-side transform — sparse zero-drops, pubkey
    canonicalization, and curve-param normalization — guaranteeing Rust encodes
    exactly the bytes Python hashes. Raises if `state` is invalid.
    """
    balances, pools, lp, nonces, fee_accumulator = build_tables(state)
    out: dict = {
        "balances": [
            {"pubkey": pk, "asset": asset, "amount": amount}
            for (pk, asset), amount in balances.get_all_balances().items()
        ],
        "pools": [
            {
                "pool_id": p.pool_id,
                "asset0": p.asset0,
                "asset1": p.asset1,
                "reserve0": p.reserve0,
                "reserve1": p.reserve1,
                "fee_bps": p.fee_bps,
                "lp_supply": p.lp_supply,
                "status": _STATUS_LABEL[p.status],
                "created_at": p.created_at,
                "curve_tag": p.curve_tag,
                "curve_params": p.curve_params,
            }
            for p in pools.values()
        ],
        "lp_balances": [
            {"pubkey": pk, "pool_id": pool, "amount": amount}
            for (pk, pool), amount in lp.get_all_balances().items()
        ],
        "lp_duration_risk": [
            {
                "pubkey": pk,
                "pool_id": pool,
                "last_mint_timestamp": m.last_mint_timestamp,
                "last_remove_timestamp": m.last_remove_timestamp,
                "churn_tier": m.churn_tier,
                "last_churn_update_timestamp": m.last_churn_update_timestamp,
            }
            for (pk, pool), m in lp.get_all_duration_risk_metadata().items()
        ],
        "nonces": [
            {"pubkey": pk, "last_nonce": n} for pk, n in nonces.get_all().items()
        ],
        "fee_accumulator": {"dust": fee_accumulator.dust},
    }
    return out


def py_eval(index: int, state: dict) -> dict:
    try:
        root = state_root_from_json(state)
    except (TypeError, ValueError, KeyError):
        return {"index": index, "ok": False}
    return {"index": index, "ok": True, "state_root": root}


def py_eval_all(states: list[dict]) -> list[dict]:
    return [py_eval(i, s) for i, s in enumerate(states)]


# --- corpora ------------------------------------------------------------------


def _pk(b: int) -> str:
    return "0x" + bytes([b] * 48).hex()


def _id32(b: int) -> str:
    return "0x" + bytes([b] * 32).hex()


def static_states() -> list[dict]:
    pk1, pk2 = _pk(1), _pk(2)
    a0, a1 = _id32(0x10), _id32(0x20)
    lp_pool = _id32(0x44)
    cpmm_30_pool = compute_pool_id(a0, a1, 30)
    cubic_pool = compute_pool_id(
        a0,
        a1,
        0,
        curve_tag="CUBIC_SUM_V1",
        curve_params='{"p":3,"q":5}',
    )
    cpmm_10000_pool = compute_pool_id(a0, a1, 10_000)
    return [
        # Empty state.
        {},
        # Balances only, given out of sorted order (root must be order-independent).
        {
            "balances": [
                {"pubkey": pk2, "asset": a1, "amount": 7},
                {"pubkey": pk1, "asset": a0, "amount": 1000},
            ]
        },
        # A full pool.
        {
            "pools": [
                {
                    "pool_id": cpmm_30_pool,
                    "asset0": a0,
                    "asset1": a1,
                    "reserve0": 500,
                    "reserve1": 700,
                    "fee_bps": 30,
                    "lp_supply": 600,
                    "status": "active",
                    "created_at": 12,
                    "curve_tag": "CPMM",
                    "curve_params": "",
                }
            ]
        },
        # Non-CPMM curve params exercise encode_bytes(utf8) on a non-empty string.
        {
            "pools": [
                {
                    "pool_id": cubic_pool,
                    "asset0": a0,
                    "asset1": a1,
                    "reserve0": 1,
                    "reserve1": 1,
                    "fee_bps": 0,
                    "lp_supply": 0,
                    "status": "frozen",
                    "created_at": 0,
                    "curve_tag": "CUBIC_SUM_V1",
                    "curve_params": '{"p":3,"q":5}',
                }
            ]
        },
        # LP balances + present duration-risk metadata (mixed optional fields).
        {
            "lp_balances": [{"pubkey": pk1, "pool_id": lp_pool, "amount": 42}],
            "lp_duration_risk": [
                {
                    "pubkey": pk1,
                    "pool_id": lp_pool,
                    "last_mint_timestamp": 5,
                    "last_remove_timestamp": None,
                    "churn_tier": 2,
                    "last_churn_update_timestamp": 9,
                },
                {
                    "pubkey": pk2,
                    "pool_id": lp_pool,
                    "last_mint_timestamp": None,
                    "last_remove_timestamp": 0,
                    "churn_tier": 0,
                    "last_churn_update_timestamp": None,
                },
            ],
        },
        # Nonces at the u32 boundary.
        {"nonces": [{"pubkey": pk1, "last_nonce": 1}, {"pubkey": pk2, "last_nonce": 0xFFFFFFFF}]},
        # Fee-accumulator dust only.
        {"fee_accumulator": {"dust": 7}},
        # Balance at the u128 boundary (in-domain max the shadow can encode).
        {"balances": [{"pubkey": pk1, "asset": a0, "amount": (1 << 128) - 1}]},
        # Everything at once.
        {
            "balances": [{"pubkey": pk1, "asset": a0, "amount": 1}],
            "pools": [
                {
                    "pool_id": cpmm_10000_pool,
                    "asset0": a0,
                    "asset1": a1,
                    "reserve0": 9,
                    "reserve1": 9,
                    "fee_bps": 10000,
                    "lp_supply": 3,
                    "status": "disabled",
                    "created_at": 99,
                    "curve_tag": "CPMM",
                    "curve_params": "",
                }
            ],
            "lp_balances": [{"pubkey": pk2, "pool_id": cpmm_10000_pool, "amount": 3}],
            "lp_duration_risk": [
                {"pubkey": pk2, "pool_id": cpmm_10000_pool, "churn_tier": 1,
                 "last_mint_timestamp": None, "last_remove_timestamp": None,
                 "last_churn_update_timestamp": None}
            ],
            "nonces": [{"pubkey": pk1, "last_nonce": 3}],
            "fee_accumulator": {"dust": 9},
        },
    ]


def _rand_amount(rng: random.Random) -> int:
    mag = rng.choice([8, 64, 112, 127])
    return rng.randrange(1, 1 << mag)


def random_states(seed: int, n: int) -> list[dict]:
    rng = random.Random(seed)
    states: list[dict] = []
    for _ in range(n):
        pks = [_pk(rng.randint(1, 40)) for _ in range(rng.randint(0, 4))]
        ids = [_id32(rng.randint(1, 40)) for _ in range(rng.randint(1, 4))]

        balances, seen_b = [], set()
        for _ in range(rng.randint(0, 5)):
            if not pks:
                break
            pk, a = rng.choice(pks), rng.choice(ids)
            if (pk, a) in seen_b:
                continue
            seen_b.add((pk, a))
            balances.append({"pubkey": pk, "asset": a, "amount": _rand_amount(rng)})

        pools, seen_p = [], set()
        for _ in range(rng.randint(0, 3)):
            # Two distinct asset bytes, strictly ordered (PoolState requires
            # asset0 < asset1 in canonical byte order).
            lo, hi = sorted(rng.sample(range(1, 41), 2))
            a0, a1 = _id32(lo), _id32(hi)
            fee_bps = rng.randint(0, 10000)
            pid = compute_pool_id(a0, a1, fee_bps)
            if pid in seen_p:
                continue
            seen_p.add(pid)
            pools.append({
                "pool_id": pid, "asset0": a0, "asset1": a1,
                "reserve0": rng.randint(0, 3_000_000_000),
                "reserve1": rng.randint(0, 3_000_000_000),
                "fee_bps": fee_bps,
                "lp_supply": rng.randint(0, 1_000_000),
                "status": rng.choice(["active", "frozen", "disabled"]),
                "created_at": rng.randint(0, 1_000_000),
                # CPMM/"" is a fixed point under curve-config normalization, so
                # build_tables never rewrites it; non-CPMM params are exercised
                # in the static corpus where the normalized form is controlled.
                "curve_tag": "CPMM",
                "curve_params": "",
            })

        pool_ids: list[str] = [str(pool["pool_id"]) for pool in pools]
        lp_balances, seen_lp = [], set()
        for _ in range(rng.randint(0, 4)):
            if not pks or not pool_ids:
                break
            pk, pid = rng.choice(pks), rng.choice(pool_ids)
            if (pk, pid) in seen_lp:
                continue
            seen_lp.add((pk, pid))
            lp_balances.append({"pubkey": pk, "pool_id": pid, "amount": _rand_amount(rng)})

        # Duration-risk metadata is keyed on LP positions. A mint timestamp may
        # only be set for a position with a live (non-zero) balance, so draw
        # duration entries from the lp_balances pairs.
        balanced_pairs: list[tuple[str, str]] = [
            (str(entry["pubkey"]), str(entry["pool_id"]))
            for entry in lp_balances
        ]
        lp_dur, seen_d = [], set()
        for _ in range(min(len(balanced_pairs), rng.randint(0, 4))):
            pk, pid = rng.choice(balanced_pairs)
            if (pk, pid) in seen_d:
                continue
            mint = rng.choice([None, 0, rng.randint(1, 10**9)])
            remove = rng.choice([None, rng.randint(0, 10**9)])
            churn = rng.choice([0, 0, rng.randint(1, 8)])
            churn_ts = rng.choice([None, rng.randint(0, 10**9)])
            # Ensure "present": at least one field non-default.
            if mint is None and remove is None and churn == 0 and churn_ts is None:
                churn = rng.randint(1, 8)
            seen_d.add((pk, pid))
            lp_dur.append({
                "pubkey": pk, "pool_id": pid,
                "last_mint_timestamp": mint, "last_remove_timestamp": remove,
                "churn_tier": churn, "last_churn_update_timestamp": churn_ts,
            })

        nonces, seen_n = [], set()
        for _ in range(rng.randint(0, 4)):
            if not pks:
                break
            pk = rng.choice(pks)
            if pk in seen_n:
                continue
            seen_n.add(pk)
            nonces.append({"pubkey": pk, "last_nonce": rng.randint(1, 0xFFFFFFFF)})

        states.append({
            "balances": balances, "pools": pools, "lp_balances": lp_balances,
            "lp_duration_risk": lp_dur, "nonces": nonces,
            "fee_accumulator": {"dust": rng.randint(0, 999)},
        })
    return states


# --- Rust bridge --------------------------------------------------------------


class StateRootShadowError(RuntimeError):
    pass


def locate_or_build_cli(*, allow_build: bool = True) -> Path:
    env_bin = os.environ.get("ZENODEX_RUNTIME_BIN")
    if env_bin:
        p = Path(env_bin)
        if not p.is_file():
            raise StateRootShadowError(f"ZENODEX_RUNTIME_BIN missing: {p}")
        return p
    if not allow_build:
        for profile in ("release", "debug"):
            candidate = RUST_RUNTIME_DIR / "target" / profile / "zenodex-runtime"
            if candidate.is_file():
                return candidate
        raise StateRootShadowError("no prebuilt zenodex-runtime binary and --no-build set")
    if shutil.which("cargo") is None:
        raise StateRootShadowError("cargo not found on PATH")
    build = subprocess.run(
        ["cargo", "build", "--quiet", "--bin", "zenodex-runtime"],
        cwd=str(RUST_RUNTIME_DIR),
        capture_output=True,
        text=True,
    )
    if build.returncode != 0:
        raise StateRootShadowError(f"cargo build failed:\n{build.stderr}")
    candidate = RUST_RUNTIME_DIR / "target" / "debug" / "zenodex-runtime"
    if not candidate.is_file():
        raise StateRootShadowError("cargo build succeeded but binary missing")
    return candidate


def run_rust(bin_path: Path, states: list[dict]) -> list[dict]:
    request = json.dumps({"cases": states})
    proc = subprocess.run(
        [str(bin_path), "verify-state-root", "-"],
        input=request,
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        raise StateRootShadowError(f"rust verify-state-root exited {proc.returncode}:\n{proc.stderr}")
    return json.loads(proc.stdout)["results"]


def diff_results(py: list[dict], rs: list[dict]) -> list[str]:
    problems: list[str] = []
    if len(py) != len(rs):
        return [f"length mismatch: python {len(py)} vs rust {len(rs)}"]
    for i, (p, r) in enumerate(zip(py, rs)):
        if bool(p["ok"]) != bool(r["ok"]):
            problems.append(f"case {i}: ok python={p['ok']} rust={r['ok']} (rust code={r.get('code')})")
            continue
        if p["ok"] and p.get("state_root") != r.get("state_root"):
            problems.append(
                f"case {i}: root python={p.get('state_root')} rust={r.get('state_root')}"
            )
    return problems
