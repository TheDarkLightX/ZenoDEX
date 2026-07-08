"""Local/testnet sealed-bid commit/reveal HTTP API.

This module is deliberately scoped to the beta GUI lane: it manages bounded
commit/reveal state, verifies reveals against commitments, settles the public
uniform-price auction, and accounts for non-reveal bonds. It does not claim
production confidentiality or perform ledger asset settlement.
"""

from __future__ import annotations

import json
import os
import time
from pathlib import Path
from typing import Any, Mapping, MutableMapping, Optional, Tuple

from src.core.sealed_bid_auction import (
    MAX_PRICE,
    MAX_UNITS,
    RevealedSealedBid,
    make_sealed_bid_commit_receipt,
    reveal_matches_commitment,
    settle_uniform_price_sealed_bids,
)
from src.core.sealed_bid_bonds import (
    MAX_BOND,
    BondedSealedBidCommit,
    SealedBidRevealRef,
    settle_sealed_bid_non_reveal_bonds,
)

ResponseT = Tuple[int, dict[str, Any]]

_SCHEMA = "zenodex/confidential-sealed-bid-api-state/v1"
_PUBLIC_SCHEMA = "zenodex/confidential-sealed-bid-api/v1"


def _parse_json_body(body: Optional[bytes]) -> tuple[Optional[dict[str, Any]], Optional[str]]:
    if body is None:
        return None, "missing_body"
    try:
        obj = json.loads(body)
    except (json.JSONDecodeError, UnicodeDecodeError):
        return None, "bad_json"
    if not isinstance(obj, dict):
        return None, "bad_body"
    return obj, None


def _clean_id(value: object, *, name: str, max_len: int = 128) -> str:
    if not isinstance(value, str):
        raise ValueError(f"bad_{name}")
    text = value.strip()
    if not text or len(text) > max_len:
        raise ValueError(f"bad_{name}")
    if any(ord(ch) < 0x20 or ord(ch) == 0x7F for ch in text):
        raise ValueError(f"bad_{name}")
    return text


def _require_int(value: object, *, name: str, minimum: int, maximum: int) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"bad_{name}")
    if value < minimum or value > maximum:
        raise ValueError(f"bad_{name}")
    return int(value)


def _load_state(state_store: MutableMapping[str, Any], state_file: str | None) -> dict[str, Any]:
    if state_store.get("_loaded") is not True:
        loaded: dict[str, Any] = {"schema": _SCHEMA, "batches": {}}
        if state_file:
            path = Path(state_file)
            if path.is_file():
                try:
                    raw = json.loads(path.read_text(encoding="utf-8"))
                    if isinstance(raw, dict) and isinstance(raw.get("batches"), dict):
                        loaded = raw
                except (OSError, json.JSONDecodeError, UnicodeDecodeError):
                    loaded = {"schema": _SCHEMA, "batches": {}}
        state_store.clear()
        state_store.update(loaded)
        state_store["_loaded"] = True
    if not isinstance(state_store.get("batches"), dict):
        state_store["batches"] = {}
    state_store["schema"] = _SCHEMA
    return dict(state_store)


def _save_state(state_store: MutableMapping[str, Any], state_file: str | None) -> None:
    if not state_file:
        return
    payload = {
        "schema": _SCHEMA,
        "batches": state_store.get("batches") if isinstance(state_store.get("batches"), dict) else {},
    }
    path = Path(state_file)
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + ".tmp")
    tmp.write_text(json.dumps(payload, sort_keys=True, separators=(",", ":")), encoding="utf-8")
    os.replace(tmp, path)


def _batch_public(batch: Mapping[str, Any]) -> dict[str, Any]:
    commits = batch.get("commits") if isinstance(batch.get("commits"), dict) else {}
    reveals = batch.get("reveals") if isinstance(batch.get("reveals"), dict) else {}
    return {
        "schema": _PUBLIC_SCHEMA,
        "batch_id": str(batch.get("batch_id") or ""),
        "phase": str(batch.get("phase") or "unknown"),
        "units_for_sale": int(batch.get("units_for_sale") or 0),
        "bond_amount": int(batch.get("bond_amount") or 0),
        "commit_count": len(commits),
        "reveal_count": len(reveals),
        "committed_bidders": sorted(str(k) for k in commits.keys()),
        "revealed_bidders": sorted(str(k) for k in reveals.keys()),
        "settlement": batch.get("settlement"),
        "bond_outcome": batch.get("bond_outcome"),
        "asset_settlement_executed": bool(batch.get("asset_settlement_executed", False)),
    }


def _status_payload(state_store: MutableMapping[str, Any], state_file: str | None) -> dict[str, Any]:
    state = _load_state(state_store, state_file)
    batches = state.get("batches") if isinstance(state.get("batches"), dict) else {}
    public_batches = [_batch_public(batch) for batch in batches.values() if isinstance(batch, dict)]
    public_batches.sort(key=lambda row: str(row.get("batch_id")))
    active = None
    for row in reversed(public_batches):
        if row.get("phase") != "settled":
            active = row
            break
    if active is None and public_batches:
        active = public_batches[-1]
    return {
        "enabled": True,
        "schema": _PUBLIC_SCHEMA,
        "asset_settlement_available": False,
        "asset_settlement_note": "ledger asset settlement is external to this local/testnet API",
        "state_persistence": "file" if state_file else "memory",
        "active_batch": active,
        "batches": public_batches[-10:],
    }


def _settlement_to_obj(settlement: Any) -> dict[str, Any]:
    return {
        "clearing_price": int(settlement.clearing_price),
        "total_filled": int(settlement.total_filled),
        "fills": [
            {
                "bidder_id": fill.bidder_id,
                "commitment": fill.commitment,
                "filled_quantity": int(fill.filled_quantity),
                "paid_price": int(fill.paid_price),
            }
            for fill in settlement.fills
        ],
    }


def _bond_outcome_to_obj(outcome: Any) -> dict[str, Any]:
    return {
        "total_bonded": int(outcome.total_bonded),
        "total_refunded": int(outcome.total_refunded),
        "total_slashed": int(outcome.total_slashed),
        "refunded_bid_count": int(outcome.refunded_bid_count),
        "slashed_bid_count": int(outcome.slashed_bid_count),
        "decisions": [
            {
                "bidder_id": decision.bidder_id,
                "commitment": decision.commitment,
                "bond_amount": int(decision.bond_amount),
                "refunded": int(decision.refunded),
                "slashed": int(decision.slashed),
            }
            for decision in outcome.decisions
        ],
    }


def _get_batch(batches: MutableMapping[str, Any], batch_id: str) -> MutableMapping[str, Any]:
    batch = batches.get(batch_id)
    if not isinstance(batch, dict):
        raise ValueError("batch_not_found")
    return batch


def handle_confidential_sealed_bid_request(
    method: str,
    path: str,
    body: Optional[bytes],
    *,
    state_store: MutableMapping[str, Any],
    state_file: str | None = None,
) -> ResponseT:
    clean_path = path.split("?", 1)[0]
    if not clean_path.startswith("/api/confidential/sealed-bid/"):
        return 404, {"ok": False, "error": "sealed_bid_route_not_found"}

    if method == "GET" and clean_path == "/api/confidential/sealed-bid/status":
        return 200, {"ok": True, "status": _status_payload(state_store, state_file)}
    if method != "POST":
        return 405, {"ok": False, "error": "method_not_allowed"}

    obj, err = _parse_json_body(body)
    if err is not None or obj is None:
        return 400, {"ok": False, "error": err or "bad_body"}

    try:
        _load_state(state_store, state_file)
        batches = state_store["batches"]

        if clean_path == "/api/confidential/sealed-bid/reset":
            batch_id = _clean_id(obj.get("batch_id"), name="batch_id")
            units_for_sale = _require_int(
                obj.get("units_for_sale"), name="units_for_sale", minimum=0, maximum=MAX_UNITS
            )
            bond_amount = _require_int(
                obj.get("bond_amount", 1), name="bond_amount", minimum=1, maximum=MAX_BOND
            )
            now = int(time.time())
            batch = {
                "schema": _SCHEMA + "/batch",
                "batch_id": batch_id,
                "phase": "commit",
                "units_for_sale": int(units_for_sale),
                "bond_amount": int(bond_amount),
                "commit_epoch": now,
                "reveal_deadline_epoch": now + 600,
                "commits": {},
                "reveals": {},
                "asset_settlement_executed": False,
            }
            batches[batch_id] = batch
            _save_state(state_store, state_file)
            return 200, {"ok": True, "batch": _batch_public(batch)}

        batch_id = _clean_id(obj.get("batch_id"), name="batch_id")
        batch = _get_batch(batches, batch_id)

        if clean_path == "/api/confidential/sealed-bid/commit":
            if batch.get("phase") != "commit":
                return 409, {"ok": False, "error": "not_commit_phase", "batch": _batch_public(batch)}
            bidder_id = _clean_id(obj.get("bidder_id"), name="bidder_id")
            commitment = _clean_id(obj.get("commitment"), name="commitment", max_len=96)
            bond_amount = _require_int(
                obj.get("bond_amount", batch.get("bond_amount", 1)),
                name="bond_amount",
                minimum=1,
                maximum=MAX_BOND,
            )
            commits = batch["commits"]
            if bidder_id in commits:
                return 409, {"ok": False, "error": "duplicate_bidder_commit"}
            receipt = make_sealed_bid_commit_receipt(
                batch_id=batch_id,
                bidder_id=bidder_id,
                commitment=commitment,
                commit_epoch=int(batch["commit_epoch"]),
                reveal_deadline_epoch=int(batch["reveal_deadline_epoch"]),
                units_for_sale=int(batch["units_for_sale"]),
            )
            commits[bidder_id] = {
                "bidder_id": bidder_id,
                "commitment": commitment,
                "bond_amount": int(bond_amount),
                "receipt": receipt,
            }
            _save_state(state_store, state_file)
            return 200, {
                "ok": True,
                "batch": _batch_public(batch),
                "receipt": receipt,
                "receipt_hash": receipt["receipt_hash"],
            }

        if clean_path == "/api/confidential/sealed-bid/open-reveal":
            if batch.get("phase") != "commit":
                return 409, {"ok": False, "error": "not_commit_phase", "batch": _batch_public(batch)}
            batch["phase"] = "reveal"
            _save_state(state_store, state_file)
            return 200, {"ok": True, "batch": _batch_public(batch)}

        if clean_path == "/api/confidential/sealed-bid/reveal":
            if batch.get("phase") != "reveal":
                return 409, {"ok": False, "error": "not_reveal_phase", "batch": _batch_public(batch)}
            bidder_id = _clean_id(obj.get("bidder_id"), name="bidder_id")
            quantity = _require_int(obj.get("quantity"), name="quantity", minimum=1, maximum=MAX_UNITS)
            limit_price = _require_int(
                obj.get("limit_price"), name="limit_price", minimum=1, maximum=MAX_PRICE
            )
            nonce = _clean_id(obj.get("nonce"), name="nonce", max_len=256)
            commits = batch["commits"]
            commit = commits.get(bidder_id)
            if not isinstance(commit, dict):
                return 404, {"ok": False, "error": "commit_not_found"}
            commitment = str(commit.get("commitment") or "")
            if not reveal_matches_commitment(
                commitment=commitment,
                quantity=int(quantity),
                limit_price=int(limit_price),
                nonce=nonce,
            ):
                return 400, {"ok": False, "error": "reveal_commitment_mismatch"}
            reveals = batch["reveals"]
            if bidder_id in reveals:
                return 409, {"ok": False, "error": "duplicate_reveal"}
            reveals[bidder_id] = {
                "bidder_id": bidder_id,
                "commitment": commitment,
                "quantity": int(quantity),
                "limit_price": int(limit_price),
            }
            _save_state(state_store, state_file)
            return 200, {"ok": True, "batch": _batch_public(batch), "reveal_admitted": True}

        if clean_path == "/api/confidential/sealed-bid/settle":
            if batch.get("phase") == "settled":
                return 200, {
                    "ok": True,
                    "batch": _batch_public(batch),
                    "settlement": batch.get("settlement"),
                    "bond_outcome": batch.get("bond_outcome"),
                    "asset_settlement_executed": bool(batch.get("asset_settlement_executed", False)),
                }
            if batch.get("phase") != "reveal":
                return 409, {"ok": False, "error": "not_reveal_phase", "batch": _batch_public(batch)}
            commits = batch["commits"]
            reveals = batch["reveals"]
            settlement = settle_uniform_price_sealed_bids(
                units_for_sale=int(batch["units_for_sale"]),
                bids=[
                    RevealedSealedBid(
                        bidder_id=str(row["bidder_id"]),
                        commitment=str(row["commitment"]),
                        quantity=int(row["quantity"]),
                        limit_price=int(row["limit_price"]),
                    )
                    for row in reveals.values()
                    if isinstance(row, dict)
                ],
            )
            bond_outcome = settle_sealed_bid_non_reveal_bonds(
                commits=[
                    BondedSealedBidCommit(
                        bidder_id=str(row["bidder_id"]),
                        commitment=str(row["commitment"]),
                        bond_amount=int(row["bond_amount"]),
                    )
                    for row in commits.values()
                    if isinstance(row, dict)
                ],
                reveals=[
                    SealedBidRevealRef(
                        bidder_id=str(row["bidder_id"]),
                        commitment=str(row["commitment"]),
                    )
                    for row in reveals.values()
                    if isinstance(row, dict)
                ],
            )
            settlement_obj = _settlement_to_obj(settlement)
            bond_obj = _bond_outcome_to_obj(bond_outcome)
            batch["phase"] = "settled"
            batch["settlement"] = settlement_obj
            batch["bond_outcome"] = bond_obj
            batch["asset_settlement_executed"] = False
            _save_state(state_store, state_file)
            return 200, {
                "ok": True,
                "batch": _batch_public(batch),
                "settlement": settlement_obj,
                "bond_outcome": bond_obj,
                "asset_settlement_executed": False,
            }

    except ValueError as exc:
        return 400, {"ok": False, "error": str(exc) or "bad_request"}
    except OSError:
        return 500, {"ok": False, "error": "sealed_bid_state_io_error"}

    return 404, {"ok": False, "error": "sealed_bid_route_not_found"}
