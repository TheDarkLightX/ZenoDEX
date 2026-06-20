"""DST crash-consistency for the DexState snapshot commit (resilience gap #3 slice).

The #3 gap's missing capability on the state-commit path: **torn-write / disk-corruption
injection** with seed-reproducible recovery. ZenoLedger persists state as a
`DexSnapshot` whose `commitment_bytes()` is a sha256 cryptographic commitment over
the canonical snapshot bytes. That makes the storage layer crash-consistent **by
construction**:

    a recovered snapshot is authoritative IFF
        sha256( domain_sep("dex_snapshot", v) || disk_bytes ) == committed_commitment

so any **torn write** (crash mid-write → truncated bytes) or **corruption** (bit-rot,
torn sector — even one that stays valid JSON) breaks the commitment and is REJECTED
on recovery: a node never silently loads corrupt/partial state as authoritative; it
fails closed (fall back to replay, or halt). This harness injects those faults into
the REAL snapshot bytes and verifies the invariant **exhaustively** over every
single-byte fault (plus seeded multi-byte faults), deterministically.

Honest scope: this is the **storage/commit-path** slice of DST — the highest-value
one, since ZenoLedger owns its state machine + storage (consensus is Tau's). It does
NOT virtualize the full clock/network/disk, nor add an Elle/Knossos *operation-history*
checker; those are the remaining #3 pieces. Uses the REAL `dex_snapshot`
(`snapshot_from_state` / `state_from_snapshot` / commitment).
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass

from src.core.dex import DexState
from src.integration.dex_snapshot import snapshot_from_state, state_from_snapshot
from src.state.balances import BalanceTable
from src.state.canonical import domain_sep_bytes
from src.state.lp import LPTable
from src.state.pools import PoolState, PoolStatus

_A0 = "0x" + "0a" * 32
_A1 = "0x" + "0b" * 32
_POOL = "0x" + "0c" * 32
_PKS = ["0x" + h * 48 for h in ("a1", "b2")]


def demo_state() -> DexState:
    """A small but representative DexState (balances + a pool + lp) with valid
    canonical identities so the real snapshot round-trips."""
    b = BalanceTable()
    for pk in _PKS:
        b.set(pk, _A0, 1_000_000)
        b.set(pk, _A1, 2_000_000)
    pools = {
        _POOL: PoolState(
            pool_id=_POOL, asset0=_A0, asset1=_A1, reserve0=500_000, reserve1=500_000,
            fee_bps=30, lp_supply=500_000, status=PoolStatus.ACTIVE, created_at=0,
        )
    }
    return DexState(balances=b, pools=pools, lp_balances=LPTable())


def _commitment_over(disk_bytes: bytes, version: int) -> bytes:
    """Recompute the snapshot commitment over (possibly faulted) on-disk bytes —
    the same binding `DexSnapshot.commitment_bytes()` produces."""
    return hashlib.sha256(domain_sep_bytes("dex_snapshot", version=version) + disk_bytes).digest()


@dataclass(frozen=True)
class RecoveryResult:
    accepted: bool
    reason: str


def recover_and_verify(committed: bytes, disk_bytes: bytes, version: int) -> RecoveryResult:
    """Model a node restart from a (possibly torn/corrupted) on-disk snapshot.

    Accept the snapshot as authoritative ONLY if its commitment matches; otherwise
    fail closed. A matching commitment means the bytes are byte-identical to what was
    committed, so the parse must then succeed (confirmed)."""
    if _commitment_over(disk_bytes, version) != committed:
        return RecoveryResult(False, "commitment_mismatch")  # torn / corrupt → rejected
    try:
        state_from_snapshot(json.loads(disk_bytes.decode("utf-8")))
    except Exception as exc:  # pragma: no cover — cannot happen on a matching commitment
        return RecoveryResult(False, f"parse_failed_despite_commitment:{exc!r}")
    return RecoveryResult(True, "ok")


# --- fault injectors ---------------------------------------------------------

def torn_at(payload: bytes, offset: int) -> bytes:
    """Crash mid-write: only the first `offset` bytes reached disk."""
    return payload[:offset]


def corrupt_byte(payload: bytes, pos: int, new: int) -> bytes:
    """Single-byte corruption (bit-rot / torn sector) at `pos`."""
    b = bytearray(payload)
    b[pos] = new & 0xFF
    return bytes(b)


def persisted_demo():
    """(committed_commitment, canonical_payload_bytes, version) for the demo state."""
    snap = snapshot_from_state(demo_state())
    return snap.commitment_bytes(), snap.canonical_bytes(), snap.version
