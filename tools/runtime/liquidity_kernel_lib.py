"""
Shared logic for the ZenoDEX liquidity-kernel Python<->Rust differential.

Sibling of ``balance_kernel_lib`` for the ``liquidity`` kernel. The liquidity
surface is stateful: a single CPMM pool (reserves + lp_supply) threads across
``tx`` steps. The ``tx`` shapes are::

    {"kind": "create_pool", "asset0": "AAA", "asset1": "BBB",
     "amount0": N, "amount1": N, "fee_bps": N, "created_at": N,
     "curve_tag": "CPMM", "curve_params": ""}
    {"kind": "add_liquidity", "amount0_desired": N, "amount1_desired": N,
     "amount0_min": N, "amount1_min": N}
    {"kind": "remove_liquidity", "lp_amount": N, "amount0_min": N,
     "amount1_min": N}

The Python authority (``src/core/liquidity.py``) raises interpolated-message
``ValueError`` / ``TypeError`` (NOT stable codes), so this module maps each
raise-site to the stable reject code the Rust kernel emits. The differential
compares *codes*, not messages. The mapping is keyed off the message-name token
(``require_int_range(name, ...)`` prefixes its message with ``name``) so the
outer field checks (``amount0_desired``) and the nested ``compute_lp_mint``
checks (``amount0``) map to *distinct* codes.

Callers must ensure the repo root is on ``sys.path``.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Optional

from src.core.liquidity import add_liquidity, create_pool, remove_liquidity
from src.state.pools import PoolState, PoolStatus, compute_pool_id, normalize_pool_asset_pair

SCHEMA_VERSION = 1
KERNEL = "liquidity"

# Domain bounds (mirror src/core/domain_limits.py).
DEX_LP_AMOUNT_MAX = 1_000_000_000
DEX_POOL_RESERVE_MAX = 3_000_000_000
DEX_LP_SUPPLY_MAX = 3_000_000_000
MIN_LP_LOCK = 1000
BPS_MAX = 10_000
U128_MAX = 2**128 - 1

REJ_MALFORMED_TX = "malformed_tx"
REJ_UNKNOWN_TX_KIND = "unknown_tx_kind"
REJ_UNKNOWN_FIELD = "unknown_field"
REJ_POOL_ID_MISMATCH = "pool_id_mismatch"

_CREATE_FIELDS = frozenset(
    {
        "kind",
        "asset0",
        "asset1",
        "amount0",
        "amount1",
        "fee_bps",
        "created_at",
        "curve_tag",
        "curve_params",
    }
)
_CREATE_REQUIRED = frozenset({"asset0", "asset1", "amount0", "amount1", "fee_bps"})
_ADD_FIELDS = frozenset(
    {"kind", "amount0_desired", "amount1_desired", "amount0_min", "amount1_min"}
)
_ADD_REQUIRED = frozenset(
    {"amount0_desired", "amount1_desired", "amount0_min", "amount1_min"}
)
_REMOVE_FIELDS = frozenset({"kind", "lp_amount", "amount0_min", "amount1_min"})
_REMOVE_REQUIRED = frozenset({"lp_amount", "amount0_min", "amount1_min"})


# --- Rust-shadow result objects ----------------------------------------------


@dataclass(frozen=True)
class LiquidityReceipt:
    kind: str
    pool_id: str
    amount0: int
    amount1: int
    lp_delta: int
    new_reserve0: int
    new_reserve1: int
    new_lp_supply: int


@dataclass(frozen=True)
class LiquidityState:
    """A single CPMM pool, threaded across trace steps.

    ``initialized`` mirrors the Rust ``Pool.initialized`` (the empty default is
    an uninitialized pool that rejects add/remove with ``pool_not_active``).
    """

    initialized: bool = False
    pool_id: str = ""
    asset0: str = ""
    asset1: str = ""
    reserve0: int = 0
    reserve1: int = 0
    fee_bps: int = 0
    lp_supply: int = 0
    created_at: int = 0

    def to_pool_state(self) -> PoolState:
        return PoolState(
            pool_id=self.pool_id,
            asset0=self.asset0,
            asset1=self.asset1,
            reserve0=self.reserve0,
            reserve1=self.reserve1,
            fee_bps=self.fee_bps,
            lp_supply=self.lp_supply,
            status=PoolStatus.ACTIVE,
            created_at=self.created_at,
            curve_tag="CPMM",
            curve_params="",
        )

    def state_root(self) -> str:
        return _state_root(self)


@dataclass(frozen=True)
class LiquidityAccepted:
    receipt: LiquidityReceipt
    state: LiquidityState


@dataclass(frozen=True)
class LiquidityRejected:
    reason: str


LiquidityResult = Any  # LiquidityAccepted | LiquidityRejected


# --- State root (matches rust-runtime liquidity::Pool::state_root) ------------


def _domain_sep(label: str, version: int) -> bytes:
    return b"zenodex:" + label.encode("ascii") + b":v" + str(version).encode("ascii") + b"\x00"


def _uvarint(value: int) -> bytes:
    out = bytearray()
    v = value
    while True:
        byte = v & 0x7F
        v >>= 7
        if v != 0:
            out.append(byte | 0x80)
        else:
            out.append(byte)
            return bytes(out)


def _encode_bytes(value: bytes) -> bytes:
    return _uvarint(len(value)) + value


def _state_root(state: LiquidityState) -> str:
    import hashlib

    buf = bytearray(_domain_sep("liquidity_pool", 1))
    buf += _uvarint(1 if state.initialized else 0)
    buf += _encode_bytes(state.pool_id.encode("utf-8"))
    buf += _encode_bytes(state.asset0.encode("utf-8"))
    buf += _encode_bytes(state.asset1.encode("utf-8"))
    buf += _uvarint(state.reserve0)
    buf += _uvarint(state.reserve1)
    buf += _uvarint(state.fee_bps)
    buf += _uvarint(state.lp_supply)
    buf += _uvarint(state.created_at)
    return "0x" + hashlib.sha256(bytes(buf)).hexdigest()


def _receipt_hash(r: LiquidityReceipt) -> str:
    import hashlib

    buf = bytearray(_domain_sep("liquidity_receipt", 1))
    buf += b"KND" + _encode_bytes(r.kind.encode("utf-8"))
    buf += b"PID" + _encode_bytes(r.pool_id.encode("utf-8"))
    buf += b"A0" + _uvarint(r.amount0)
    buf += b"A1" + _uvarint(r.amount1)
    buf += b"LPD" + _uvarint(r.lp_delta)
    buf += b"R0" + _uvarint(r.new_reserve0)
    buf += b"R1" + _uvarint(r.new_reserve1)
    buf += b"LPS" + _uvarint(r.new_lp_supply)
    return "0x" + hashlib.sha256(bytes(buf)).hexdigest()


def receipt_hash(r: LiquidityReceipt) -> str:
    return _receipt_hash(r)


# --- Exception -> stable reject code mapping ---------------------------------
#
# `require_int_range(name, ...)` raises ValueError with a message that STARTS
# with the field `name` ("amount0_desired must be >= 1: ..."), so both the
# `< minimum` and `> maximum` branches for a given field map to the same field
# code. TypeError("... must be an int") on a pool scalar is impossible here (we
# always pass ints). The outer add-liquidity field names differ from the nested
# `compute_lp_mint` field names ("amount0_desired" vs "amount0"), which is how
# `used == 0` -> `mint_amount0_out_of_domain` is distinguished.


def _classify_create_error(exc: BaseException) -> str:
    msg = str(exc)
    if isinstance(exc, TypeError):
        return "invalid_asset_type"
    if "canonical order" in msg:
        return "assets_not_canonical"
    if msg.startswith("amount0 "):
        return "amount0_out_of_domain"
    if msg.startswith("amount1 "):
        return "amount1_out_of_domain"
    if msg.startswith("fee_bps "):
        return "fee_bps_out_of_domain"
    if msg.startswith("created_at "):
        return "created_at_out_of_domain"
    if "insufficient initial liquidity" in msg:
        return "insufficient_initial_liquidity"
    # Malformed real 32-byte hex asset id, raised by canonical_hex_fixed_allow_0x
    # inside normalize_pool_asset_pair (compute_pool_id @ liquidity.py:72). The
    # messages are "<name> must be valid hex" and
    # "<name> must be 32 bytes (hex length 64)" - both contain "hex". This MUST
    # precede the curve branch (a malformed-hex message never names a curve, but
    # the ordering keeps the intent explicit) and follows the canonical-order
    # branch above (same-canonical pairs already map to assets_not_canonical).
    if "hex" in msg:
        return "invalid_asset_hex"
    # normalize_curve_config rejections (non-CPMM tag / bad params).
    if "curve_tag" in msg or "curve_params" in msg or "CPMM" in msg or "param" in msg:
        return "unsupported_curve_tag"
    raise AssertionError(f"unmapped create_pool error: {msg!r}")


def _classify_add_error(exc: BaseException) -> str:
    msg = str(exc)
    if isinstance(exc, TypeError):
        # Pool scalar non-int; not reachable with int inputs, but map safely.
        raise AssertionError(f"unexpected TypeError in add_liquidity: {msg!r}")
    if "hex" in msg:
        return "invalid_asset_hex"
    if "canonical order" in msg:
        return "assets_not_canonical"
    if msg.startswith("fee_bps ") or "fee_bps must be" in msg:
        return "fee_bps_out_of_domain"
    if "not active" in msg:
        return "pool_not_active"
    if msg.startswith("pool_state.reserve0 "):
        return "reserve0_out_of_domain"
    if msg.startswith("pool_state.reserve1 "):
        return "reserve1_out_of_domain"
    if msg.startswith("pool_state.lp_supply "):
        return "lp_supply_out_of_domain"
    if "empty pool" in msg:
        return "empty_pool"
    if msg.startswith("amount0_desired "):
        return "amount0_desired_out_of_domain"
    if msg.startswith("amount1_desired "):
        return "amount1_desired_out_of_domain"
    if msg.startswith("amount0_min "):
        return "amount0_min_out_of_domain"
    if msg.startswith("amount1_min "):
        return "amount1_min_out_of_domain"
    if msg.startswith("amount0_used "):
        return "amount0_used_below_min"
    if msg.startswith("amount1_used "):
        return "amount1_used_below_min"
    # Nested compute_lp_mint re-validates the USED amounts under the names
    # "amount0"/"amount1" (cpmm.py:285-286) -> degenerate-ratio reject.
    if msg.startswith("amount0 "):
        return "mint_amount0_out_of_domain"
    if msg.startswith("amount1 "):
        return "mint_amount1_out_of_domain"
    if "exceed reserve0 domain" in msg:
        return "reserve0_domain_exceeded"
    if "exceed reserve1 domain" in msg:
        return "reserve1_domain_exceeded"
    # Nested compute_lp_mint with lp_supply==0 takes the isqrt initial-mint
    # branch (reachable from add when the pool has reserves but zero LP supply,
    # advisor point A); a too-small `sqrt(used0*used1)` rejects with the SAME
    # code the Rust kernel emits for the create path.
    if "insufficient initial liquidity" in msg:
        return "insufficient_initial_liquidity"
    if "non-positive" in msg:
        return "lp_non_positive"
    raise AssertionError(f"unmapped add_liquidity error: {msg!r}")


def _classify_remove_error(exc: BaseException) -> str:
    msg = str(exc)
    if isinstance(exc, TypeError):
        raise AssertionError(f"unexpected TypeError in remove_liquidity: {msg!r}")
    if "hex" in msg:
        return "invalid_asset_hex"
    if "canonical order" in msg:
        return "assets_not_canonical"
    if msg.startswith("fee_bps ") or "fee_bps must be" in msg:
        return "fee_bps_out_of_domain"
    if "not active" in msg:
        return "pool_not_active"
    if msg.startswith("pool_state.reserve0 "):
        return "reserve0_out_of_domain"
    if msg.startswith("pool_state.reserve1 "):
        return "reserve1_out_of_domain"
    if msg.startswith("pool_state.lp_supply "):
        return "lp_supply_out_of_domain"
    if msg.startswith("lp_amount "):
        return "lp_amount_out_of_domain"
    if msg.startswith("amount0_min "):
        return "amount0_min_out_of_domain"
    if msg.startswith("amount1_min "):
        return "amount1_min_out_of_domain"
    if "burn more LP than supply" in msg:
        return "burn_exceeds_supply"
    if msg.startswith("amount0_out "):
        return "amount0_out_below_min"
    if msg.startswith("amount1_out "):
        return "amount1_out_below_min"
    raise AssertionError(f"unmapped remove_liquidity error: {msg!r}")


# --- tx field validation (mirrors the Rust CLI structural checks) ------------


def _is_strict_int(v: Any) -> bool:
    return isinstance(v, int) and not isinstance(v, bool)


def _field_int_or_reject(value: Any, *, has_max: bool) -> Optional[int]:
    """Return an int suitable for the kernel, or None if structurally malformed.

    Mirrors the Rust CLI: integer-shaped, and for max-bounded fields a negative
    saturates to a value the kernel range-check will reject; for unbounded
    fields (``created_at``) a negative must surface as the specific reject (so
    the caller handles it via the kernel, which checks ``minimum=0``).
    """
    if not _is_strict_int(value):
        return None
    return int(value)


def _create_pre_created_at_reject(
    *,
    asset_type_ok: bool,
    asset0: Any,
    asset1: Any,
    amount0: int,
    amount1: int,
    fee_bps: int,
) -> str | None:
    """Rejects that precede `created_at` in `src/core/liquidity.py::create_pool`.

    REVIEW [B -> A-]: the Rust CLI must defer negative or oversized
    `created_at` until after asset/amount/fee checks. Keeping the same ordered
    helper in the Python shadow makes precedence drift visible in the
    Python<->Rust differential instead of hidden inside a trace fixture.
    """
    if not asset_type_ok:
        return "invalid_asset_type"
    if asset0 >= asset1:
        return "assets_not_canonical"
    if not (1 <= amount0 <= DEX_LP_AMOUNT_MAX):
        return "amount0_out_of_domain"
    if not (1 <= amount1 <= DEX_LP_AMOUNT_MAX):
        return "amount1_out_of_domain"
    if not (0 <= fee_bps <= BPS_MAX):
        return "fee_bps_out_of_domain"
    return None


def _active_snapshot_reject(state: LiquidityState) -> str | None:
    """Reject malformed active snapshots before add/remove arithmetic.

    REVIEW [B -> A-]: the first differential shadow delegated this to
    PoolState construction, which raised AssertionError for bad active snapshots
    such as asset0 >= asset1 or fee_bps > 10000. The Rust op-path accepts JSON
    snapshots directly, so the shadow must return stable in-band reject codes
    for the same boundary.
    """
    if not state.initialized:
        return "pool_not_active"
    if not isinstance(state.asset0, str) or not isinstance(state.asset1, str):
        return "invalid_asset_type"
    try:
        c0, c1 = normalize_pool_asset_pair(state.asset0, state.asset1)
    except ValueError as exc:
        return "invalid_asset_hex" if "hex" in str(exc) else "assets_not_canonical"
    if (c0, c1) != (state.asset0, state.asset1):
        return "assets_not_canonical"
    if not _is_strict_int(state.fee_bps) or not (0 <= state.fee_bps <= BPS_MAX):
        return "fee_bps_out_of_domain"
    # REVIEW [B+ -> A]: a snapshot with canonical assets/fee but a forged pool_id
    # used to pass both this Python shadow and the Rust CLI. The pool id is part
    # of the committed state root and liquidity receipt, so explicit verifier
    # snapshots must bind it to the same CPMM derivation as create_pool.
    if not isinstance(state.pool_id, str):
        return REJ_POOL_ID_MISMATCH
    if state.pool_id != compute_pool_id(state.asset0, state.asset1, state.fee_bps):
        return REJ_POOL_ID_MISMATCH
    if not _is_strict_int(state.reserve0) or state.reserve0 < 0:
        return "reserve0_out_of_domain"
    if not _is_strict_int(state.reserve1) or state.reserve1 < 0:
        return "reserve1_out_of_domain"
    if not _is_strict_int(state.lp_supply) or state.lp_supply < 0:
        return "lp_supply_out_of_domain"
    return None


def apply_tx(state: LiquidityState, tx: Any) -> LiquidityResult:
    """Apply one trace ``tx`` to ``state``; never raises on malformed input."""
    if not isinstance(tx, dict):
        return LiquidityRejected(REJ_MALFORMED_TX)
    kind = tx.get("kind")
    if kind == "create_pool":
        return _apply_create(state, tx)
    if kind == "add_liquidity":
        return _apply_add(state, tx)
    if kind == "remove_liquidity":
        return _apply_remove(state, tx)
    return LiquidityRejected(REJ_UNKNOWN_TX_KIND)


def _apply_create(state: LiquidityState, tx: dict) -> LiquidityResult:
    extra = set(tx) - _CREATE_FIELDS
    if extra:
        return LiquidityRejected(f"{REJ_UNKNOWN_FIELD}:{sorted(extra)[0]}")
    if not _CREATE_REQUIRED <= set(tx):
        return LiquidityRejected(REJ_MALFORMED_TX)

    asset0 = tx["asset0"]
    asset1 = tx["asset1"]
    # asset type: must be JSON strings (the create_pool TypeError boundary).
    asset_type_ok = isinstance(asset0, str) and isinstance(asset1, str)

    for key in ("amount0", "amount1", "fee_bps"):
        if not _is_strict_int(tx[key]):
            return LiquidityRejected(REJ_MALFORMED_TX)
    created_at = tx.get("created_at", 0)
    if "created_at" in tx and not _is_strict_int(created_at):
        return LiquidityRejected(REJ_MALFORMED_TX)
    curve_tag = tx.get("curve_tag", "CPMM")
    curve_params = tx.get("curve_params", "")

    early = _create_pre_created_at_reject(
        asset_type_ok=asset_type_ok,
        asset0=asset0,
        asset1=asset1,
        amount0=tx["amount0"],
        amount1=tx["amount1"],
        fee_bps=tx["fee_bps"],
    )
    if early is not None:
        return LiquidityRejected(early)
    if not (0 <= created_at <= U128_MAX):
        return LiquidityRejected("created_at_out_of_domain")

    # Exotic curves are out of in-kernel scope: stable-reject any non-CPMM tag
    # (and any non-empty params) before calling the authority, mirroring Rust.
    if not (isinstance(curve_tag, str) and curve_tag.upper() == "CPMM"):
        return LiquidityRejected("unsupported_curve_tag")
    if curve_params not in (None, "", {}):
        # CPMM with non-empty params -> normalize_curve_config rejects, which we
        # surface as unsupported_curve_tag (same scoping decision).
        return LiquidityRejected("unsupported_curve_tag")

    try:
        pool_id, ps, lp_minted = create_pool(
            asset0,
            asset1,
            tx["amount0"],
            tx["amount1"],
            tx["fee_bps"],
            "pk",
            created_at=created_at,
            curve_tag="CPMM",
            curve_params="",
        )
    except (ValueError, TypeError) as exc:
        return LiquidityRejected(_classify_create_error(exc))

    next_state = LiquidityState(
        initialized=True,
        pool_id=pool_id,
        asset0=ps.asset0,
        asset1=ps.asset1,
        reserve0=ps.reserve0,
        reserve1=ps.reserve1,
        fee_bps=ps.fee_bps,
        lp_supply=ps.lp_supply,
        created_at=ps.created_at,
    )
    receipt = LiquidityReceipt(
        kind="create_pool",
        pool_id=pool_id,
        amount0=ps.reserve0,
        amount1=ps.reserve1,
        lp_delta=lp_minted,
        new_reserve0=ps.reserve0,
        new_reserve1=ps.reserve1,
        new_lp_supply=ps.lp_supply,
    )
    return LiquidityAccepted(receipt=receipt, state=next_state)


def _apply_add(state: LiquidityState, tx: dict) -> LiquidityResult:
    extra = set(tx) - _ADD_FIELDS
    if extra:
        return LiquidityRejected(f"{REJ_UNKNOWN_FIELD}:{sorted(extra)[0]}")
    if not _ADD_REQUIRED <= set(tx):
        return LiquidityRejected(REJ_MALFORMED_TX)
    for key in _ADD_REQUIRED:
        if not _is_strict_int(tx[key]):
            return LiquidityRejected(REJ_MALFORMED_TX)

    snapshot_reject = _active_snapshot_reject(state)
    if snapshot_reject is not None:
        return LiquidityRejected(snapshot_reject)

    try:
        used0, used1, lp_minted = add_liquidity(
            state.to_pool_state(),
            tx["amount0_desired"],
            tx["amount1_desired"],
            tx["amount0_min"],
            tx["amount1_min"],
        )
    except (ValueError, TypeError) as exc:
        return LiquidityRejected(_classify_add_error(exc))

    new_reserve0 = state.reserve0 + used0
    new_reserve1 = state.reserve1 + used1
    new_lp_supply = state.lp_supply + lp_minted
    next_state = LiquidityState(
        initialized=True,
        pool_id=state.pool_id,
        asset0=state.asset0,
        asset1=state.asset1,
        reserve0=new_reserve0,
        reserve1=new_reserve1,
        fee_bps=state.fee_bps,
        lp_supply=new_lp_supply,
        created_at=state.created_at,
    )
    receipt = LiquidityReceipt(
        kind="add_liquidity",
        pool_id=state.pool_id,
        amount0=used0,
        amount1=used1,
        lp_delta=lp_minted,
        new_reserve0=new_reserve0,
        new_reserve1=new_reserve1,
        new_lp_supply=new_lp_supply,
    )
    return LiquidityAccepted(receipt=receipt, state=next_state)


def _apply_remove(state: LiquidityState, tx: dict) -> LiquidityResult:
    extra = set(tx) - _REMOVE_FIELDS
    if extra:
        return LiquidityRejected(f"{REJ_UNKNOWN_FIELD}:{sorted(extra)[0]}")
    if not _REMOVE_REQUIRED <= set(tx):
        return LiquidityRejected(REJ_MALFORMED_TX)
    for key in _REMOVE_REQUIRED:
        if not _is_strict_int(tx[key]):
            return LiquidityRejected(REJ_MALFORMED_TX)

    snapshot_reject = _active_snapshot_reject(state)
    if snapshot_reject is not None:
        return LiquidityRejected(snapshot_reject)

    try:
        out0, out1 = remove_liquidity(
            state.to_pool_state(),
            tx["lp_amount"],
            tx["amount0_min"],
            tx["amount1_min"],
        )
    except (ValueError, TypeError) as exc:
        return LiquidityRejected(_classify_remove_error(exc))

    new_reserve0 = state.reserve0 - out0
    new_reserve1 = state.reserve1 - out1
    new_lp_supply = state.lp_supply - tx["lp_amount"]
    next_state = LiquidityState(
        initialized=True,
        pool_id=state.pool_id,
        asset0=state.asset0,
        asset1=state.asset1,
        reserve0=new_reserve0,
        reserve1=new_reserve1,
        fee_bps=state.fee_bps,
        lp_supply=new_lp_supply,
        created_at=state.created_at,
    )
    receipt = LiquidityReceipt(
        kind="remove_liquidity",
        pool_id=state.pool_id,
        amount0=out0,
        amount1=out1,
        lp_delta=tx["lp_amount"],
        new_reserve0=new_reserve0,
        new_reserve1=new_reserve1,
        new_lp_supply=new_lp_supply,
    )
    return LiquidityAccepted(receipt=receipt, state=next_state)


# --- Trace / replay (shaped like the Rust CLI output) ------------------------


def replay_txs(txs: list) -> dict:
    """Replay a bare ``tx`` list from the empty pool; shape like the Rust CLI."""
    state = LiquidityState()
    initial_root = state.state_root()
    results: list[dict] = []
    for i, tx in enumerate(txs):
        pre_root = state.state_root()
        result = apply_tx(state, tx)
        if isinstance(result, LiquidityAccepted):
            state = result.state
            results.append(
                {
                    "index": i,
                    "accept": True,
                    "reject_reason": None,
                    "receipt_hash": _receipt_hash(result.receipt),
                    "pre_state_root": pre_root,
                    "post_state_root": state.state_root(),
                }
            )
        else:
            results.append(
                {
                    "index": i,
                    "accept": False,
                    "reject_reason": result.reason,
                    "receipt_hash": None,
                    "pre_state_root": pre_root,
                    "post_state_root": pre_root,
                }
            )
    return {
        "version": SCHEMA_VERSION,
        "kernel": KERNEL,
        "initial_state_root": initial_root,
        "final_state_root": state.state_root(),
        "results": results,
    }


# --- Golden smoke trace ------------------------------------------------------

_A0 = "AAA"
_A1 = "BBB"


def smoke_tx_sequence() -> list[dict]:
    """Deterministic liquidity corpus: create/add/remove happy paths, every
    rounding edge, every rejection code, and reject-precedence pairs."""
    return [
        # create: isqrt(1e12)=1e6 -> mint 999000
        {
            "kind": "create_pool",
            "asset0": _A0,
            "asset1": _A1,
            "amount0": 1_000_000,
            "amount1": 1_000_000,
            "fee_bps": 30,
            "created_at": 0,
            "curve_tag": "CPMM",
            "curve_params": "",
        },
        # add proportional: used == desired, lp == 100000
        {
            "kind": "add_liquidity",
            "amount0_desired": 100_000,
            "amount1_desired": 100_000,
            "amount0_min": 0,
            "amount1_min": 0,
        },
        # remove: burn 50000 of 1.1M supply
        {
            "kind": "remove_liquidity",
            "lp_amount": 50_000,
            "amount0_min": 0,
            "amount1_min": 0,
        },
        # add with skewed desired -> used drift via floor cross-product
        {
            "kind": "add_liquidity",
            "amount0_desired": 100_000,
            "amount1_desired": 200_000,
            "amount0_min": 0,
            "amount1_min": 0,
        },
        # add below-min reject
        {
            "kind": "add_liquidity",
            "amount0_desired": 1000,
            "amount1_desired": 1000,
            "amount0_min": 5000,
            "amount1_min": 0,
        },
        # remove output below min
        {
            "kind": "remove_liquidity",
            "lp_amount": 1,
            "amount0_min": 100,
            "amount1_min": 0,
        },
        # burn exceeds supply
        {
            "kind": "remove_liquidity",
            "lp_amount": 5_000_000,
            "amount0_min": 0,
            "amount1_min": 0,
        },
        # unknown field
        {
            "kind": "add_liquidity",
            "amount0_desired": 1,
            "amount1_desired": 1,
            "amount0_min": 0,
            "amount1_min": 0,
            "memo": "x",
        },
        # unknown tx kind
        {"kind": "swap", "amount0_desired": 1},
        # malformed (missing field)
        {"kind": "remove_liquidity", "lp_amount": 1, "amount0_min": 0},
    ]


def build_smoke_trace() -> dict:
    state = LiquidityState()
    initial_root = state.state_root()
    steps: list[dict] = []
    for tx in smoke_tx_sequence():
        pre_root = state.state_root()
        result = apply_tx(state, tx)
        if isinstance(result, LiquidityAccepted):
            steps.append(
                {
                    "tx": tx,
                    "expected_accept": True,
                    "expected_reject_reason": None,
                    "post_state_root": result.state.state_root(),
                    "receipt_hash": _receipt_hash(result.receipt),
                }
            )
            state = result.state
        else:
            steps.append(
                {
                    "tx": tx,
                    "expected_accept": False,
                    "expected_reject_reason": result.reason,
                    "post_state_root": pre_root,
                    "receipt_hash": None,
                }
            )
    return {
        "version": SCHEMA_VERSION,
        "kernel": KERNEL,
        "initial_state_root": initial_root,
        "steps": steps,
        "final_state_root": state.state_root(),
    }


class ReplayMismatch(Exception):
    """Raised when a replay disagrees with the recorded golden trace."""


def replay_trace(trace: dict) -> dict:
    if not isinstance(trace, dict):
        raise ReplayMismatch("trace must be a JSON object")
    if trace.get("version") != SCHEMA_VERSION:
        raise ReplayMismatch(f"unsupported trace version: {trace.get('version')!r}")
    if trace.get("kernel") != KERNEL:
        raise ReplayMismatch(f"unsupported kernel: {trace.get('kernel')!r}")
    state = LiquidityState()
    if trace.get("initial_state_root") != state.state_root():
        raise ReplayMismatch("initial_state_root mismatch")
    steps = trace.get("steps")
    if not isinstance(steps, list):
        raise ReplayMismatch("steps must be a list")

    n_accept = 0
    n_reject = 0
    for i, rec in enumerate(steps):
        if not isinstance(rec, dict):
            raise ReplayMismatch(f"step {i}: record must be an object")
        pre_root = state.state_root()
        result = apply_tx(state, rec.get("tx"))
        if isinstance(result, LiquidityAccepted):
            n_accept += 1
            if rec.get("expected_accept") is not True:
                raise ReplayMismatch(f"step {i}: accepted but trace expected reject")
            if rec.get("receipt_hash") != _receipt_hash(result.receipt):
                raise ReplayMismatch(f"step {i}: receipt_hash mismatch")
            if rec.get("post_state_root") != result.state.state_root():
                raise ReplayMismatch(f"step {i}: post_state_root mismatch")
            state = result.state
        else:
            n_reject += 1
            if rec.get("expected_accept") is not False:
                raise ReplayMismatch(
                    f"step {i}: rejected ({result.reason}) but trace expected accept"
                )
            if rec.get("expected_reject_reason") != result.reason:
                raise ReplayMismatch(
                    f"step {i}: reject reason mismatch trace={rec.get('expected_reject_reason')} "
                    f"computed={result.reason}"
                )
            if rec.get("post_state_root") != pre_root:
                raise ReplayMismatch(f"step {i}: rejected step changed post_state_root")

    if trace.get("final_state_root") != state.state_root():
        raise ReplayMismatch("final_state_root mismatch")
    return {
        "steps": len(steps),
        "accepted": n_accept,
        "rejected": n_reject,
        "final_state_root": state.state_root(),
    }


if __name__ == "__main__":
    import json
    import sys

    print(json.dumps(build_smoke_trace(), indent=2))
    sys.exit(0)
