"""Local/testnet in-memory sealed-bid commit/reveal/settle API.

This handler orchestrates the existing *pure* sealed-bid primitives
(:mod:`src.core.sealed_bid_auction` and :mod:`src.core.sealed_bid_bonds`) over a
mutex-protected in-memory batch table. It exists so the redesigned Confidential
Workbench UI can drive a real commit -> reveal -> settle lifecycle on a local
testnet node.

HONEST CLAIM BOUNDARY (load-bearing — do not soften):

- This surface makes **no production security claim** and **no TEE/FHE
  confidentiality claim**. ``production_security_claim`` is ``False``.
- All state is **in-memory** on a single node and is lost on restart. There is no
  consensus, no persistence, and no replay-protected ledger here.
- Settlement is **accounting-only**: it computes a uniform-price clearing and a
  non-reveal bond outcome but moves **no real funds or assets**.
  ``asset_settlement_available`` is ``False`` and ``asset_settlement_executed`` is
  always ``False`` — the UI correctly renders "external adapter required".
- **No authentication.** ``bidder_id`` is an *unauthenticated* free-form label.
  The commit -> reveal binding is purely *cryptographic* — a reveal must hash to
  the previously-committed digest, so a copier who lacks the preimage cannot
  reveal — but there is **no wallet-signature or account authentication**. A
  demo-authed caller can commit under any ``bidder_id``. ``signature_auth_available``
  and ``account_authenticated`` are both ``False``. The MISSING piece for any
  production sealed-bid surface is signature-bound bidders; it is marked here, not
  hidden.

The handler is fail-closed: any malformed input, wrong phase, bidder-slot
violation, or unknown batch yields a deterministic reject with a stable code and
leaves state unchanged (reject-is-no-op). ``reset`` additionally refuses to
silently clobber an in-progress batch (commits recorded, not yet settled) unless
``force`` is explicitly ``true``. The shell (api_server) gates this whole surface
behind ``CONFIDENTIAL_ATTESTATION_API_ENABLED`` AND an explicit per-feature
``sealed_bid_enabled`` (env ``CONFIDENTIAL_SEALED_BID_ENABLED``, default OFF), so
enabling attestation alone does NOT expose this write surface.
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from typing import Any, Dict, Mapping, Optional, Tuple

from ..core.sealed_bid_auction import (
    MAX_PRICE,
    MAX_UNITS,
    RevealedSealedBid,
    make_sealed_bid_commit_receipt,
    reveal_matches_commitment,
    settle_uniform_price_sealed_bids,
    verify_commit_receipt,
)
from ..core.sealed_bid_bonds import (
    MAX_BOND,
    BondedSealedBidCommit,
    SealedBidRevealRef,
    settle_sealed_bid_non_reveal_bonds,
)

ResponseT = Tuple[int, Dict[str, Any]]

MAX_POST_BODY = 65_536
MAX_BATCHES = 256
MAX_BIDDERS_PER_BATCH = 64
_HEX64_RE_LEN = 64

# Phase machine: commit -> reveal -> settled. Mirrors the
# sealed_bid_commit_reveal_gate_v1 kernel (Commit -> Reveal -> Complete) but with
# UI-facing lower-case names. ``settled`` is terminal.
PHASE_COMMIT = "commit"
PHASE_REVEAL = "reveal"
PHASE_SETTLED = "settled"

CLAIM_SCOPE = "local_testnet_in_memory_sealed_bid_accounting"
PRODUCTION_SECURITY_CLAIM = False

# In-memory batches use a fixed bounded epoch window. These are display/receipt
# fields only; this surface has no real epoch clock.
_COMMIT_EPOCH = 0
_REVEAL_DEADLINE_EPOCH = 1


# --- Domain-typed parse helpers (validate at boundary) ---------------------


def _parse_json_body(body: Optional[bytes]) -> tuple[Optional[dict[str, Any]], Optional[str]]:
    if body is None or len(body) == 0:
        return None, "empty_body"
    if len(body) > MAX_POST_BODY:
        return None, "body_too_large"
    try:
        obj = json.loads(body)
    except (json.JSONDecodeError, UnicodeDecodeError):
        return None, "invalid_json"
    if not isinstance(obj, dict):
        return None, "expected_object"
    return obj, None


def _req_str(body: Mapping[str, Any], *, name: str, max_len: int = 128) -> str:
    value = body.get(name)
    if not isinstance(value, str):
        raise ValueError(f"{name} must be a string")
    text = value.strip()
    if not text:
        raise ValueError(f"{name} must be non-empty")
    if len(text) > max_len:
        raise ValueError(f"{name} too long")
    return text


def _req_int(body: Mapping[str, Any], *, name: str, lo: int, hi: int) -> int:
    value = body.get(name)
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"{name} must be an int")
    if value < lo or value > hi:
        raise ValueError(f"{name} must be in [{lo}, {hi}]")
    return int(value)


def _is_commitment(value: object) -> bool:
    # The browser/UI computes the commitment with
    # ``src.core.sealed_bid_auction.sealed_bid_reveal_hash``, which returns a
    # 0x-prefixed 64-char lowercase hex digest. Accept exactly that shape.
    if not isinstance(value, str):
        return False
    text = value.strip().lower()
    if not text.startswith("0x"):
        return False
    hexpart = text[2:]
    if len(hexpart) != _HEX64_RE_LEN:
        return False
    return all(c in "0123456789abcdef" for c in hexpart)


def _req_commitment(body: Mapping[str, Any], *, name: str = "commitment") -> str:
    value = body.get(name)
    if not _is_commitment(value):
        raise ValueError(f"{name} must be a 0x-prefixed 64-char hex string")
    # Preserve the 0x-prefixed form so it compares equal to the value returned by
    # ``sealed_bid_reveal_hash`` during reveal verification.
    return str(value).strip().lower()


# --- Functional-core batch state -------------------------------------------


@dataclass(frozen=True)
class _BondedCommit:
    bidder_id: str
    commitment: str
    bond_amount: int
    receipt_hash: str


@dataclass(frozen=True)
class _RevealedBid:
    bidder_id: str
    commitment: str
    quantity: int
    limit_price: int


@dataclass
class _Batch:
    batch_id: str
    units_for_sale: int
    phase: str = PHASE_COMMIT
    commits: Dict[str, _BondedCommit] = field(default_factory=dict)
    reveals: Dict[str, _RevealedBid] = field(default_factory=dict)


@dataclass
class SealedBidBatchTable:
    """Mutex-protected (by the caller) in-memory store of sealed-bid batches.

    The api_server holds a ``threading.Lock`` around every mutating call so this
    type does not need its own locking. It is deliberately simple, bounded, and
    free of any I/O or persistence.
    """

    _batches: Dict[str, _Batch] = field(default_factory=dict)

    def get(self, batch_id: str) -> Optional[_Batch]:
        return self._batches.get(batch_id)

    def reset(self, batch: _Batch) -> None:
        self._batches[batch.batch_id] = batch

    def count(self) -> int:
        return len(self._batches)


# --- Settlement (accounting-only, pure) ------------------------------------


def _settle_batch(batch: _Batch) -> dict[str, Any]:
    """Compute uniform-price clearing + non-reveal bond outcome.

    Pure: derives the result from the recorded commits/reveals. Moves no funds.
    """
    revealed_bids = [
        RevealedSealedBid(
            bidder_id=rb.bidder_id,
            commitment=rb.commitment,
            quantity=int(rb.quantity),
            limit_price=int(rb.limit_price),
        )
        for rb in batch.reveals.values()
    ]
    settlement = settle_uniform_price_sealed_bids(
        units_for_sale=int(batch.units_for_sale),
        bids=revealed_bids,
    )
    bond_outcome = settle_sealed_bid_non_reveal_bonds(
        commits=[
            BondedSealedBidCommit(
                bidder_id=c.bidder_id,
                commitment=c.commitment,
                bond_amount=int(c.bond_amount),
            )
            for c in batch.commits.values()
        ],
        reveals=[
            SealedBidRevealRef(bidder_id=rb.bidder_id, commitment=rb.commitment)
            for rb in batch.reveals.values()
        ],
    )
    return {
        "settlement": {
            "clearing_price": int(settlement.clearing_price),
            "total_filled": int(settlement.total_filled),
            "fills": [
                {
                    "bidder_id": f.bidder_id,
                    "commitment": f.commitment,
                    "filled_quantity": int(f.filled_quantity),
                    "paid_price": int(f.paid_price),
                }
                for f in settlement.fills
            ],
        },
        "bond_outcome": {
            "total_bonded": int(bond_outcome.total_bonded),
            "total_refunded": int(bond_outcome.total_refunded),
            "total_slashed": int(bond_outcome.total_slashed),
            "refunded_bid_count": int(bond_outcome.refunded_bid_count),
            "slashed_bid_count": int(bond_outcome.slashed_bid_count),
        },
    }


def _claim_envelope() -> dict[str, Any]:
    return {
        "claim_scope": CLAIM_SCOPE,
        "production_security_claim": PRODUCTION_SECURITY_CLAIM,
        "asset_settlement_available": False,
        # Honest auth boundary (machine-checkable): bidder_id is an UNAUTHENTICATED
        # label. This surface does commit->reveal *cryptographic* binding only; it
        # performs NO wallet-signature or account authentication. Production
        # sealed-bid requires signature-bound bidders.
        "signature_auth_available": False,
        "account_authenticated": False,
    }


# --- Handlers (one per endpoint) -------------------------------------------


def _handle_status(table: SealedBidBatchTable, *, sealed_bid_enabled: bool) -> ResponseT:
    return 200, {
        "ok": True,
        "status": {
            "enabled": True,
            "sealed_bid_enabled": bool(sealed_bid_enabled),
            "active_batches": int(table.count()),
            "phases": [PHASE_COMMIT, PHASE_REVEAL, PHASE_SETTLED],
            "non_claims": [
                "no production security claim",
                "no TEE/FHE confidentiality claim",
                "in-memory single-node state only; lost on restart",
                "settlement is accounting-only and moves no funds or assets",
                "bidder_id is an unauthenticated label: no wallet-signature or "
                "account auth; commit->reveal binding is cryptographic (preimage), "
                "NOT identity. A demo-authed caller may commit under any bidder_id. "
                "MISSING for production: signature-bound bidders.",
            ],
            **_claim_envelope(),
            "endpoints": [
                "GET  /api/confidential/sealed-bid/status",
                "POST /api/confidential/sealed-bid/reset",
                "POST /api/confidential/sealed-bid/commit",
                "POST /api/confidential/sealed-bid/open-reveal",
                "POST /api/confidential/sealed-bid/reveal",
                "POST /api/confidential/sealed-bid/settle",
            ],
        },
    }


def _handle_reset(table: SealedBidBatchTable, body: Mapping[str, Any]) -> ResponseT:
    try:
        batch_id = _req_str(body, name="batch_id")
        units_for_sale = _req_int(body, name="units_for_sale", lo=0, hi=MAX_UNITS)
        # bond_amount validated for shape parity with commit; it bounds the
        # per-bidder bond a client may post for this batch.
        _ = _req_int(body, name="bond_amount", lo=1, hi=MAX_BOND)
    except ValueError as exc:
        return 400, {"ok": False, "error": "bad_request", "details": str(exc)}

    existing = table.get(batch_id)
    if existing is None and table.count() >= MAX_BATCHES:
        return 429, {"ok": False, "error": "too_many_batches"}

    # Anti-griefing: refuse to silently wipe a batch that already has recorded
    # commits and is not yet settled, unless the caller explicitly passes
    # force=true. This is NOT identity auth (bidder_id is unauthenticated — see
    # the claim envelope); it only stops an accidental or hostile reset from
    # discarding an in-progress batch's commits.
    if (
        existing is not None
        and existing.phase != PHASE_SETTLED
        and len(existing.commits) > 0
        and body.get("force") is not True
    ):
        return 409, {
            "ok": False,
            "error": "batch_in_progress",
            "phase": existing.phase,
            "commit_count": len(existing.commits),
        }

    # reset is idempotent re-initialization: a fresh batch in the commit phase.
    table.reset(_Batch(batch_id=batch_id, units_for_sale=int(units_for_sale)))
    return 200, {
        "ok": True,
        "batch": {"batch_id": batch_id, "phase": PHASE_COMMIT, "units_for_sale": int(units_for_sale)},
        **_claim_envelope(),
    }


def _handle_commit(table: SealedBidBatchTable, body: Mapping[str, Any]) -> ResponseT:
    try:
        batch_id = _req_str(body, name="batch_id")
        bidder_id = _req_str(body, name="bidder_id")
        commitment = _req_commitment(body, name="commitment")
        bond_amount = _req_int(body, name="bond_amount", lo=1, hi=MAX_BOND)
    except ValueError as exc:
        return 400, {"ok": False, "error": "bad_request", "details": str(exc)}

    batch = table.get(batch_id)
    if batch is None:
        return 404, {"ok": False, "error": "unknown_batch"}
    if batch.phase != PHASE_COMMIT:
        return 409, {"ok": False, "error": "phase_not_commit", "phase": batch.phase}
    # Bidder-slot binding (NOT identity auth — bidder_id is unauthenticated): one
    # commit per bidder_id per batch (no re-commit / overwrite).
    if bidder_id in batch.commits:
        return 409, {"ok": False, "error": "bidder_already_committed"}
    # Reject a copied commitment from a different bidder. A copier cannot reveal
    # it (they lack the preimage), so this only prevents a confusing griefing
    # state; the (bidder_id, commitment) settlement keys would otherwise collide.
    if any(c.commitment == commitment for c in batch.commits.values()):
        return 409, {"ok": False, "error": "duplicate_commitment"}
    if len(batch.commits) >= MAX_BIDDERS_PER_BATCH:
        return 429, {"ok": False, "error": "too_many_bidders"}

    # Build the public commit receipt. Note: quantity/price/nonce are NOT inputs
    # here — the commit receipt deliberately exposes only the commitment.
    try:
        receipt = make_sealed_bid_commit_receipt(
            batch_id=batch_id,
            bidder_id=bidder_id,
            commitment=commitment,
            commit_epoch=_COMMIT_EPOCH,
            reveal_deadline_epoch=_REVEAL_DEADLINE_EPOCH,
            units_for_sale=int(batch.units_for_sale),
        )
    except ValueError as exc:
        return 400, {"ok": False, "error": "bad_commit", "details": str(exc)}

    ok, reason = verify_commit_receipt(receipt)
    if not ok:
        # Defense-in-depth: never admit a receipt we cannot re-verify. No state
        # mutation has happened yet, so this is a clean reject.
        return 500, {"ok": False, "error": "commit_receipt_self_check_failed", "details": reason}

    receipt_hash = str(receipt.get("receipt_hash") or "")
    # Commit only after all checks pass (validate-before-mutate).
    batch.commits[bidder_id] = _BondedCommit(
        bidder_id=bidder_id,
        commitment=commitment,
        bond_amount=int(bond_amount),
        receipt_hash=receipt_hash,
    )
    return 200, {
        "ok": True,
        "batch": {"batch_id": batch_id, "phase": batch.phase, "commit_count": len(batch.commits)},
        "bidder_id": bidder_id,
        "commitment": commitment,
        "receipt_hash": receipt_hash,
        "receipt": receipt,
        **_claim_envelope(),
    }


def _handle_open_reveal(table: SealedBidBatchTable, body: Mapping[str, Any]) -> ResponseT:
    try:
        batch_id = _req_str(body, name="batch_id")
    except ValueError as exc:
        return 400, {"ok": False, "error": "bad_request", "details": str(exc)}

    batch = table.get(batch_id)
    if batch is None:
        return 404, {"ok": False, "error": "unknown_batch"}
    if batch.phase != PHASE_COMMIT:
        return 409, {"ok": False, "error": "phase_not_commit", "phase": batch.phase}
    batch.phase = PHASE_REVEAL
    return 200, {
        "ok": True,
        "batch": {"batch_id": batch_id, "phase": batch.phase, "commit_count": len(batch.commits)},
        **_claim_envelope(),
    }


def _handle_reveal(table: SealedBidBatchTable, body: Mapping[str, Any]) -> ResponseT:
    try:
        batch_id = _req_str(body, name="batch_id")
        bidder_id = _req_str(body, name="bidder_id")
        quantity = _req_int(body, name="quantity", lo=1, hi=MAX_UNITS)
        limit_price = _req_int(body, name="limit_price", lo=1, hi=MAX_PRICE)
        nonce = _req_str(body, name="nonce", max_len=256)
    except ValueError as exc:
        return 400, {"ok": False, "error": "bad_request", "details": str(exc)}

    batch = table.get(batch_id)
    if batch is None:
        return 404, {"ok": False, "error": "unknown_batch"}
    if batch.phase != PHASE_REVEAL:
        return 409, {"ok": False, "error": "phase_not_reveal", "phase": batch.phase}
    # Bidder-slot binding (NOT identity auth): a reveal must reference a bidder_id
    # that actually committed in this batch.
    commit = batch.commits.get(bidder_id)
    if commit is None:
        return 404, {"ok": False, "error": "no_commit_for_bidder"}
    if bidder_id in batch.reveals:
        return 409, {"ok": False, "error": "bidder_already_revealed"}
    # The reveal must hash to the previously-committed commitment (binding check).
    if not reveal_matches_commitment(
        commitment=commit.commitment,
        quantity=int(quantity),
        limit_price=int(limit_price),
        nonce=nonce,
    ):
        return 400, {"ok": False, "error": "reveal_commitment_mismatch"}

    batch.reveals[bidder_id] = _RevealedBid(
        bidder_id=bidder_id,
        commitment=commit.commitment,
        quantity=int(quantity),
        limit_price=int(limit_price),
    )
    return 200, {
        "ok": True,
        "batch": {
            "batch_id": batch_id,
            "phase": batch.phase,
            "commit_count": len(batch.commits),
            "reveal_count": len(batch.reveals),
        },
        "bidder_id": bidder_id,
        "commitment": commit.commitment,
        **_claim_envelope(),
    }


def _handle_settle(table: SealedBidBatchTable, body: Mapping[str, Any]) -> ResponseT:
    try:
        batch_id = _req_str(body, name="batch_id")
    except ValueError as exc:
        return 400, {"ok": False, "error": "bad_request", "details": str(exc)}

    batch = table.get(batch_id)
    if batch is None:
        return 404, {"ok": False, "error": "unknown_batch"}
    if batch.phase != PHASE_REVEAL:
        return 409, {"ok": False, "error": "phase_not_reveal", "phase": batch.phase}

    try:
        outcome = _settle_batch(batch)
    except ValueError as exc:
        # Pure settlement rejected the recorded state — leave the batch in REVEAL.
        return 400, {"ok": False, "error": "settlement_rejected", "details": str(exc)}

    batch.phase = PHASE_SETTLED
    # Honesty: even if the client asked for asset settlement, this surface has no
    # ledger adapter, so we never execute it and say so plainly.
    return 200, {
        "ok": True,
        "batch": {
            "batch_id": batch_id,
            "phase": batch.phase,
            "commit_count": len(batch.commits),
            "reveal_count": len(batch.reveals),
        },
        "settlement": outcome["settlement"],
        "bond_outcome": outcome["bond_outcome"],
        "asset_settlement_executed": False,
        **_claim_envelope(),
    }


# --- Public entrypoint -----------------------------------------------------


def handle_confidential_sealed_bid_request(
    method: str,
    path: str,
    raw_body: Optional[bytes],
    *,
    batch_table: SealedBidBatchTable,
    sealed_bid_enabled: bool,
) -> ResponseT:
    """Total dispatcher for the local in-memory sealed-bid endpoints.

    Returns ``(status_code, json_body)``. The caller (api_server) is responsible
    for the env gate, demo-auth, and holding a mutex around mutating calls.
    """
    if not sealed_bid_enabled:
        # Fail-closed: the whole sub-flow is disabled on this node.
        return 503, {"ok": False, "error": "sealed_bid_disabled"}

    if method == "GET" and path == "/api/confidential/sealed-bid/status":
        return _handle_status(batch_table, sealed_bid_enabled=sealed_bid_enabled)

    if method != "POST":
        return 405, {"ok": False, "error": "method_not_allowed"}

    obj, err = _parse_json_body(raw_body)
    if err is not None or obj is None:
        return 400, {"ok": False, "error": str(err or "invalid_request")}

    if path == "/api/confidential/sealed-bid/reset":
        return _handle_reset(batch_table, obj)
    if path == "/api/confidential/sealed-bid/commit":
        return _handle_commit(batch_table, obj)
    if path == "/api/confidential/sealed-bid/open-reveal":
        return _handle_open_reveal(batch_table, obj)
    if path == "/api/confidential/sealed-bid/reveal":
        return _handle_reveal(batch_table, obj)
    if path == "/api/confidential/sealed-bid/settle":
        return _handle_settle(batch_table, obj)

    return 404, {"ok": False, "error": "not_found"}
