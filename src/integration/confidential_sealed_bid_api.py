"""Mounted confidential sealed-bid commit/reveal API.

The mounted API is deliberately narrow:
- commitments are supplied by the client or enclave; the server never computes
  a commitment from private quantity, price, and nonce during commit
- reveal validates the supplied private values against the public commitment
- settlement uses the deterministic in-repo uniform-price and non-reveal bond
  kernels

Durability is optional through ``CONFIDENTIAL_SEALED_BID_STATE_FILE`` in
``api_server.py``. In-memory mode is useful for local smoke tests; a configured
state file gives the API restart-safe auction state for production-adjacent
deployments while asset movement remains an external integration.
"""

from __future__ import annotations

import json
import os
import re
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Mapping, Optional, Tuple

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

MAX_POST_BODY = 96_000
MAX_BATCHES = 128
MAX_COMMITS_PER_BATCH = 512
DEFAULT_BATCH_ID = "local-sealed-bid-v1"
DEFAULT_UNITS_FOR_SALE = 10
DEFAULT_COMMIT_EPOCH = 1
DEFAULT_REVEAL_DEADLINE_EPOCH = 2
DEFAULT_BOND_AMOUNT = 5
ResponseT = Tuple[int, dict[str, Any]]
_ID_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_.:/-]{0,127}$")
_COMMITMENT_RE = re.compile(r"^0x[0-9a-fA-F]{64}$")
_PRIVATE_COMMIT_FIELDS = frozenset({"direction", "limit_price", "nonce", "order_side", "quantity", "side"})


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


def _request_id(body: Mapping[str, Any], *, name: str, default: str | None = None) -> str:
    value = body.get(name, default)
    if not isinstance(value, str) or not _ID_RE.fullmatch(value.strip()):
        raise ValueError(f"bad_{name}")
    return value.strip()


def _request_int(
    body: Mapping[str, Any],
    *,
    name: str,
    default: int | None = None,
    lo: int,
    hi: int,
) -> int:
    value = body.get(name, default)
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"bad_{name}")
    if value < lo or value > hi:
        raise ValueError(f"bad_{name}")
    return int(value)


def _request_commitment(body: Mapping[str, Any], *, name: str = "commitment") -> str:
    value = body.get(name)
    if not isinstance(value, str) or not _COMMITMENT_RE.fullmatch(value.strip()):
        raise ValueError(f"bad_{name}")
    return value.strip().lower()


def _private_commit_fields(body: Mapping[str, Any]) -> tuple[str, ...]:
    return tuple(sorted(str(key) for key in body if str(key) in _PRIVATE_COMMIT_FIELDS))


def _reject_unknown_fields(body: Mapping[str, Any], *, allowed: set[str]) -> tuple[int, dict[str, Any]] | None:
    unknown = tuple(sorted(str(key) for key in body if str(key) not in allowed))
    if not unknown:
        return None
    return 400, {"ok": False, "error": "unknown_fields", "fields": list(unknown)}


def _env_str(name: str, default: str) -> str:
    raw = os.environ.get(name)
    if raw is None:
        return default
    value = raw.strip()
    return value if value else default


def _env_bool(name: str, default: bool = False) -> bool:
    raw = os.environ.get(name)
    if raw is None or not raw.strip():
        return bool(default)
    return raw.strip().lower() in {"1", "true", "yes", "on"}


def _atomic_write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp_name = tempfile.mkstemp(prefix=f".{path.name}.", suffix=".tmp", dir=str(path.parent))
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as fh:
            json.dump(payload, fh, sort_keys=True, separators=(",", ":"))
            fh.write("\n")
            fh.flush()
            os.fsync(fh.fileno())
        os.replace(tmp_name, path)
    except Exception:
        try:
            os.unlink(tmp_name)
        except OSError:
            pass
        raise


@dataclass
class SealedBidCommitRecord:
    bidder_id: str
    commitment: str
    bond_amount: int
    commit_receipt: dict[str, Any]

    def to_public_dict(self) -> dict[str, Any]:
        return {
            "bidder_id": self.bidder_id,
            "commitment": self.commitment,
            "bond_amount": int(self.bond_amount),
            "receipt_hash": self.commit_receipt.get("receipt_hash"),
        }

    def to_json(self) -> dict[str, Any]:
        return {
            "bidder_id": self.bidder_id,
            "commitment": self.commitment,
            "bond_amount": int(self.bond_amount),
            "commit_receipt": self.commit_receipt,
        }

    @classmethod
    def from_json(cls, obj: Mapping[str, Any]) -> "SealedBidCommitRecord":
        record = cls(
            bidder_id=str(obj["bidder_id"]),
            commitment=str(obj["commitment"]).lower(),
            bond_amount=int(obj["bond_amount"]),
            commit_receipt=dict(obj["commit_receipt"]),
        )
        if not _ID_RE.fullmatch(record.bidder_id):
            raise ValueError("bad_commit_bidder_id")
        if not _COMMITMENT_RE.fullmatch(record.commitment):
            raise ValueError("bad_commitment")
        if record.bond_amount <= 0 or record.bond_amount > MAX_BOND:
            raise ValueError("bad_bond_amount")
        ok, err = verify_commit_receipt(record.commit_receipt)
        if not ok:
            raise ValueError(f"bad_commit_receipt:{err}")
        body = record.commit_receipt.get("body")
        if not isinstance(body, Mapping):
            raise ValueError("bad_commit_receipt_body")
        if body.get("bidder_id") != record.bidder_id or str(body.get("commitment")).lower() != record.commitment:
            raise ValueError("commit_receipt_record_mismatch")
        return record


@dataclass
class SealedBidRevealRecord:
    bidder_id: str
    commitment: str
    quantity: int
    limit_price: int

    def to_public_dict(self) -> dict[str, Any]:
        return {
            "bidder_id": self.bidder_id,
            "commitment": self.commitment,
            "quantity": int(self.quantity),
            "limit_price": int(self.limit_price),
        }

    def to_json(self) -> dict[str, Any]:
        return self.to_public_dict()

    @classmethod
    def from_json(cls, obj: Mapping[str, Any]) -> "SealedBidRevealRecord":
        record = cls(
            bidder_id=str(obj["bidder_id"]),
            commitment=str(obj["commitment"]).lower(),
            quantity=int(obj["quantity"]),
            limit_price=int(obj["limit_price"]),
        )
        if not _ID_RE.fullmatch(record.bidder_id):
            raise ValueError("bad_reveal_bidder_id")
        if not _COMMITMENT_RE.fullmatch(record.commitment):
            raise ValueError("bad_reveal_commitment")
        if record.quantity <= 0 or record.quantity > MAX_UNITS:
            raise ValueError("bad_reveal_quantity")
        if record.limit_price <= 0 or record.limit_price > MAX_PRICE:
            raise ValueError("bad_reveal_limit_price")
        return record


@dataclass
class SealedBidBatch:
    batch_id: str
    units_for_sale: int = DEFAULT_UNITS_FOR_SALE
    commit_epoch: int = DEFAULT_COMMIT_EPOCH
    reveal_deadline_epoch: int = DEFAULT_REVEAL_DEADLINE_EPOCH
    default_bond_amount: int = DEFAULT_BOND_AMOUNT
    phase: str = "commit"
    commits: dict[str, SealedBidCommitRecord] = field(default_factory=dict)
    reveals: dict[str, SealedBidRevealRecord] = field(default_factory=dict)
    settlement: dict[str, Any] | None = None
    bond_outcome: dict[str, Any] | None = None

    def to_public_dict(self, *, include_records: bool = False) -> dict[str, Any]:
        payload: dict[str, Any] = {
            "batch_id": self.batch_id,
            "phase": self.phase,
            "units_for_sale": int(self.units_for_sale),
            "commit_epoch": int(self.commit_epoch),
            "reveal_deadline_epoch": int(self.reveal_deadline_epoch),
            "default_bond_amount": int(self.default_bond_amount),
            "commit_count": len(self.commits),
            "reveal_count": len(self.reveals),
            "settled": self.phase == "settled",
            "settlement": self.settlement,
            "bond_outcome": self.bond_outcome,
            "asset_settlement": None,
            "asset_settlement_executed": False,
        }
        if include_records:
            payload["commits"] = [
                self.commits[key].to_public_dict() for key in sorted(self.commits)
            ]
            payload["reveals"] = [
                self.reveals[key].to_public_dict() for key in sorted(self.reveals)
            ]
        return payload

    def to_json(self) -> dict[str, Any]:
        return {
            "batch_id": self.batch_id,
            "units_for_sale": int(self.units_for_sale),
            "commit_epoch": int(self.commit_epoch),
            "reveal_deadline_epoch": int(self.reveal_deadline_epoch),
            "default_bond_amount": int(self.default_bond_amount),
            "phase": self.phase,
            "commits": {key: record.to_json() for key, record in sorted(self.commits.items())},
            "reveals": {key: record.to_json() for key, record in sorted(self.reveals.items())},
            "settlement": self.settlement,
            "bond_outcome": self.bond_outcome,
            "asset_settlement": None,
        }

    @classmethod
    def from_json(cls, obj: Mapping[str, Any]) -> "SealedBidBatch":
        commits_obj = obj.get("commits")
        reveals_obj = obj.get("reveals")
        if not isinstance(commits_obj, Mapping) or not isinstance(reveals_obj, Mapping):
            raise ValueError("bad_batch_records")
        if isinstance(obj.get("asset_settlement"), Mapping):
            raise ValueError("retired_asset_settlement_state")
        batch = cls(
            batch_id=str(obj["batch_id"]),
            units_for_sale=int(obj["units_for_sale"]),
            commit_epoch=int(obj["commit_epoch"]),
            reveal_deadline_epoch=int(obj["reveal_deadline_epoch"]),
            default_bond_amount=int(obj["default_bond_amount"]),
            phase=str(obj["phase"]),
            settlement=dict(obj["settlement"]) if isinstance(obj.get("settlement"), Mapping) else None,
            bond_outcome=dict(obj["bond_outcome"]) if isinstance(obj.get("bond_outcome"), Mapping) else None,
        )
        if not _ID_RE.fullmatch(batch.batch_id):
            raise ValueError("bad_batch_id")
        if batch.units_for_sale < 0 or batch.units_for_sale > MAX_UNITS:
            raise ValueError("bad_units_for_sale")
        if batch.commit_epoch < 0 or batch.reveal_deadline_epoch < batch.commit_epoch:
            raise ValueError("bad_epoch_window")
        if batch.default_bond_amount <= 0 or batch.default_bond_amount > MAX_BOND:
            raise ValueError("bad_default_bond_amount")
        if batch.phase not in {"commit", "reveal", "settled"}:
            raise ValueError("bad_batch_phase")
        for key, value in commits_obj.items():
            if not isinstance(value, Mapping):
                raise ValueError("bad_commit_record")
            batch.commits[str(key)] = SealedBidCommitRecord.from_json(value)
        for key, value in reveals_obj.items():
            if not isinstance(value, Mapping):
                raise ValueError("bad_reveal_record")
            batch.reveals[str(key)] = SealedBidRevealRecord.from_json(value)
        if len(batch.commits) > MAX_COMMITS_PER_BATCH:
            raise ValueError("too_many_commits")
        for key, record in batch.commits.items():
            if key != record.bidder_id:
                raise ValueError("commit_key_mismatch")
        for key, record in batch.reveals.items():
            if key != record.bidder_id:
                raise ValueError("reveal_key_mismatch")
            commit = batch.commits.get(key)
            if commit is None or commit.commitment != record.commitment:
                raise ValueError("reveal_commit_mismatch")
        return batch


class ConfidentialSealedBidTable:
    """Small bounded sealed-bid state table with optional JSON durability."""

    def __init__(self, *, state_path: str | None = None) -> None:
        self.state_path = str(state_path or "").strip()
        self.batches: dict[str, SealedBidBatch] = {}
        self.last_error = ""
        if self.state_path:
            self._load()

    @property
    def storage_mode(self) -> str:
        return "durable_json" if self.state_path else "memory"

    def _load(self) -> None:
        path = Path(self.state_path)
        if not path.exists():
            return
        try:
            obj = json.loads(path.read_text(encoding="utf-8"))
            batches_obj = obj.get("batches") if isinstance(obj, Mapping) else None
            if not isinstance(batches_obj, Mapping):
                raise ValueError("bad_state_file")
            loaded: dict[str, SealedBidBatch] = {}
            for key, value in batches_obj.items():
                if not isinstance(value, Mapping):
                    raise ValueError("bad_batch")
                loaded[str(key)] = SealedBidBatch.from_json(value)
            if len(loaded) > MAX_BATCHES:
                raise ValueError("too_many_batches")
            self.batches = loaded
        except Exception as exc:
            self.last_error = f"load_failed:{exc}"
            self.batches = {}

    def _persist(self) -> None:
        if not self.state_path:
            return
        payload = {
            "schema": "zenodex/confidential_sealed_bid_state/v1",
            "batches": {key: batch.to_json() for key, batch in sorted(self.batches.items())},
        }
        _atomic_write_json(Path(self.state_path), payload)

    def _get_batch(self, batch_id: str) -> SealedBidBatch | None:
        return self.batches.get(batch_id)

    def reset_batch(
        self,
        *,
        batch_id: str,
        units_for_sale: int,
        commit_epoch: int,
        reveal_deadline_epoch: int,
        default_bond_amount: int,
    ) -> SealedBidBatch:
        if reveal_deadline_epoch < commit_epoch:
            raise ValueError("bad_epoch_window")
        if batch_id in self.batches:
            raise ValueError("batch_already_exists")
        if batch_id not in self.batches and len(self.batches) >= MAX_BATCHES:
            raise ValueError("too_many_batches")
        batch = SealedBidBatch(
            batch_id=batch_id,
            units_for_sale=units_for_sale,
            commit_epoch=commit_epoch,
            reveal_deadline_epoch=reveal_deadline_epoch,
            default_bond_amount=default_bond_amount,
            phase="commit",
        )
        self.batches[batch_id] = batch
        self._persist()
        return batch

    def commit(
        self,
        *,
        batch_id: str,
        bidder_id: str,
        commitment: str,
        bond_amount: int | None = None,
    ) -> tuple[SealedBidBatch, SealedBidCommitRecord]:
        batch = self._get_batch(batch_id)
        if batch is None:
            batch = self.reset_batch(
                batch_id=batch_id,
                units_for_sale=DEFAULT_UNITS_FOR_SALE,
                commit_epoch=DEFAULT_COMMIT_EPOCH,
                reveal_deadline_epoch=DEFAULT_REVEAL_DEADLINE_EPOCH,
                default_bond_amount=DEFAULT_BOND_AMOUNT,
            )
        if batch.phase != "commit":
            raise ValueError("commit_phase_closed")
        if bidder_id in batch.commits:
            raise ValueError("duplicate_commit")
        if len(batch.commits) >= MAX_COMMITS_PER_BATCH:
            raise ValueError("too_many_commits")
        if any(record.commitment == commitment for record in batch.commits.values()):
            raise ValueError("duplicate_commitment")
        bond = int(batch.default_bond_amount if bond_amount is None else bond_amount)
        if bond <= 0 or bond > MAX_BOND:
            raise ValueError("bad_bond_amount")
        # Anti-griefing (Codex F2): the batch default_bond_amount is the REQUIRED
        # floor, not merely a fallback. A bidder may over-bond but not under-bond;
        # otherwise a non-revealing bidder could post bond=1 against a batch reset
        # with a high anti-griefing bond and underpay the non-reveal slash, since
        # settlement (settle_sealed_bid_non_reveal_bonds) slashes the POSTED bond.
        if bond < batch.default_bond_amount:
            raise ValueError("bond_below_required")
        receipt = make_sealed_bid_commit_receipt(
            batch_id=batch.batch_id,
            bidder_id=bidder_id,
            commitment=commitment,
            commit_epoch=batch.commit_epoch,
            reveal_deadline_epoch=batch.reveal_deadline_epoch,
            units_for_sale=batch.units_for_sale,
        )
        receipt_ok, receipt_error = verify_commit_receipt(receipt)
        if not receipt_ok:
            raise ValueError(f"bad_commit_receipt:{receipt_error}")
        record = SealedBidCommitRecord(
            bidder_id=bidder_id,
            commitment=commitment,
            bond_amount=bond,
            commit_receipt=receipt,
        )
        batch.commits[bidder_id] = record
        self._persist()
        return batch, record

    def open_reveal(self, *, batch_id: str) -> SealedBidBatch:
        batch = self._get_batch(batch_id)
        if batch is None:
            raise ValueError("unknown_batch")
        if batch.phase != "commit":
            raise ValueError("bad_phase")
        if not batch.commits:
            raise ValueError("empty_commit_set")
        batch.phase = "reveal"
        self._persist()
        return batch

    def reveal(
        self,
        *,
        batch_id: str,
        bidder_id: str,
        quantity: int,
        limit_price: int,
        nonce: str,
    ) -> tuple[SealedBidBatch, SealedBidRevealRecord]:
        batch = self._get_batch(batch_id)
        if batch is None:
            raise ValueError("unknown_batch")
        if batch.phase != "reveal":
            raise ValueError("reveal_phase_closed")
        commit = batch.commits.get(bidder_id)
        if commit is None:
            raise ValueError("unknown_commit")
        if bidder_id in batch.reveals:
            raise ValueError("duplicate_reveal")
        if not reveal_matches_commitment(
            commitment=commit.commitment,
            quantity=quantity,
            limit_price=limit_price,
            nonce=nonce,
        ):
            raise ValueError("commitment_mismatch")
        record = SealedBidRevealRecord(
            bidder_id=bidder_id,
            commitment=commit.commitment,
            quantity=quantity,
            limit_price=limit_price,
        )
        batch.reveals[bidder_id] = record
        self._persist()
        return batch, record

    def _settlement_payloads(self, batch: SealedBidBatch) -> tuple[dict[str, Any], dict[str, Any]]:
        settlement = settle_uniform_price_sealed_bids(
            units_for_sale=batch.units_for_sale,
            bids=(
                RevealedSealedBid(
                    bidder_id=record.bidder_id,
                    commitment=record.commitment,
                    quantity=record.quantity,
                    limit_price=record.limit_price,
                )
                for record in batch.reveals.values()
            ),
        )
        bond_outcome = settle_sealed_bid_non_reveal_bonds(
            commits=(
                BondedSealedBidCommit(
                    bidder_id=record.bidder_id,
                    commitment=record.commitment,
                    bond_amount=record.bond_amount,
                )
                for record in batch.commits.values()
            ),
            reveals=(
                SealedBidRevealRef(
                    bidder_id=record.bidder_id,
                    commitment=record.commitment,
                )
                for record in batch.reveals.values()
            ),
        )
        settlement_payload = {
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
        bond_payload = {
            "total_bonded": int(bond_outcome.total_bonded),
            "total_refunded": int(bond_outcome.total_refunded),
            "total_slashed": int(bond_outcome.total_slashed),
            "refunded_bid_count": int(bond_outcome.refunded_bid_count),
            "slashed_bid_count": int(bond_outcome.slashed_bid_count),
            "decisions": [
                {
                    "bidder_id": decision.bidder_id,
                    "commitment": decision.commitment,
                    "bond_amount": int(decision.bond_amount),
                    "refunded": int(decision.refunded),
                    "slashed": int(decision.slashed),
                }
                for decision in bond_outcome.decisions
            ],
        }
        return settlement_payload, bond_payload

    def settlement_preview(self, *, batch_id: str) -> tuple[SealedBidBatch, dict[str, Any], dict[str, Any]]:
        batch = self._get_batch(batch_id)
        if batch is None:
            raise ValueError("unknown_batch")
        if batch.phase == "settled":
            if not isinstance(batch.settlement, Mapping) or not isinstance(batch.bond_outcome, Mapping):
                raise ValueError("settled_batch_missing_payload")
            return batch, dict(batch.settlement), dict(batch.bond_outcome)
        if batch.phase != "reveal":
            raise ValueError("reveal_phase_not_open")
        settlement, bond_outcome = self._settlement_payloads(batch)
        return batch, settlement, bond_outcome

    def record_settlement(
        self,
        *,
        batch_id: str,
        settlement: Mapping[str, Any],
        bond_outcome: Mapping[str, Any],
    ) -> SealedBidBatch:
        batch = self._get_batch(batch_id)
        if batch is None:
            raise ValueError("unknown_batch")
        batch.settlement = dict(settlement)
        batch.bond_outcome = dict(bond_outcome)
        batch.phase = "settled"
        self._persist()
        return batch

    def settle(self, *, batch_id: str) -> SealedBidBatch:
        batch, settlement, bond_outcome = self.settlement_preview(batch_id=batch_id)
        if batch.phase == "settled":
            return batch
        return self.record_settlement(
            batch_id=batch_id,
            settlement=settlement,
            bond_outcome=bond_outcome,
        )

    def status(self) -> dict[str, Any]:
        return {
            "schema": "zenodex/confidential_sealed_bid_api_status/v1",
            "enabled": True,
            "storage_mode": self.storage_mode,
            "state_path_configured": bool(self.state_path),
            "state_load_error": self.last_error or None,
            "max_batches": MAX_BATCHES,
            "max_commits_per_batch": MAX_COMMITS_PER_BATCH,
            "production_scope": {
                "commit_reveal_semantics": True,
                "restart_safe_state": bool(self.state_path and not self.last_error),
                "asset_settlement": False,
                "private_commit_fields_on_commit": False,
            },
            "endpoints": [
                "GET /api/confidential/sealed-bid/status",
                "POST /api/confidential/sealed-bid/reset",
                "POST /api/confidential/sealed-bid/commit",
                "POST /api/confidential/sealed-bid/open-reveal",
                "POST /api/confidential/sealed-bid/reveal",
                "POST /api/confidential/sealed-bid/settle",
            ],
            "batches": [
                self.batches[key].to_public_dict(include_records=True)
                for key in sorted(self.batches)
            ],
        }


def _status_payload(
    table: ConfidentialSealedBidTable | None,
) -> ResponseT:
    if table is None:
        return 503, {"ok": False, "error": "confidential_sealed_bid_table_unavailable"}
    status = table.status()
    status["asset_settlement_available"] = False
    status["local_testnet_scope"] = {
        "asset_settlement": False,
        "asset_settlement_mode": "unavailable",
        "production_security_claim": False,
    }
    return 200, {"ok": True, "status": status}


def _handle_reset(body: Mapping[str, Any], *, table: ConfidentialSealedBidTable | None) -> ResponseT:
    if table is None:
        return 503, {"ok": False, "error": "confidential_sealed_bid_table_unavailable"}
    unknown = _reject_unknown_fields(
        body,
        allowed={"batch_id", "units_for_sale", "commit_epoch", "reveal_deadline_epoch", "bond_amount"},
    )
    if unknown is not None:
        return unknown
    try:
        batch = table.reset_batch(
            batch_id=_request_id(body, name="batch_id", default=DEFAULT_BATCH_ID),
            units_for_sale=_request_int(
                body,
                name="units_for_sale",
                default=DEFAULT_UNITS_FOR_SALE,
                lo=0,
                hi=MAX_UNITS,
            ),
            commit_epoch=_request_int(
                body,
                name="commit_epoch",
                default=DEFAULT_COMMIT_EPOCH,
                lo=0,
                hi=2**31 - 1,
            ),
            reveal_deadline_epoch=_request_int(
                body,
                name="reveal_deadline_epoch",
                default=DEFAULT_REVEAL_DEADLINE_EPOCH,
                lo=0,
                hi=2**31 - 1,
            ),
            default_bond_amount=_request_int(
                body,
                name="bond_amount",
                default=DEFAULT_BOND_AMOUNT,
                lo=1,
                hi=MAX_BOND,
            ),
        )
    except Exception as exc:
        return 400, {"ok": False, "error": str(exc)}
    return 200, {"ok": True, "batch": batch.to_public_dict(include_records=True)}


def _handle_commit(body: Mapping[str, Any], *, table: ConfidentialSealedBidTable | None) -> ResponseT:
    if table is None:
        return 503, {"ok": False, "error": "confidential_sealed_bid_table_unavailable"}
    leaked = _private_commit_fields(body)
    if leaked:
        return 400, {
            "ok": False,
            "error": "private_commit_fields_forbidden",
            "private_fields": list(leaked),
        }
    unknown = _reject_unknown_fields(
        body,
        allowed={"batch_id", "bidder_id", "commitment", "bond_amount"},
    )
    if unknown is not None:
        return unknown
    try:
        bond_amount = None
        if "bond_amount" in body:
            bond_amount = _request_int(body, name="bond_amount", lo=1, hi=MAX_BOND)
        batch, record = table.commit(
            batch_id=_request_id(body, name="batch_id", default=DEFAULT_BATCH_ID),
            bidder_id=_request_id(body, name="bidder_id"),
            commitment=_request_commitment(body),
            bond_amount=bond_amount,
        )
    except Exception as exc:
        return 400, {"ok": False, "error": str(exc)}
    return 200, {
        "ok": True,
        "batch": batch.to_public_dict(include_records=False),
        "commit": record.to_public_dict(),
        "commit_receipt": record.commit_receipt,
        "receipt_hash": record.commit_receipt.get("receipt_hash"),
        "private_fields_accepted": False,
    }


def _handle_open_reveal(body: Mapping[str, Any], *, table: ConfidentialSealedBidTable | None) -> ResponseT:
    if table is None:
        return 503, {"ok": False, "error": "confidential_sealed_bid_table_unavailable"}
    unknown = _reject_unknown_fields(body, allowed={"batch_id"})
    if unknown is not None:
        return unknown
    try:
        batch = table.open_reveal(batch_id=_request_id(body, name="batch_id", default=DEFAULT_BATCH_ID))
    except Exception as exc:
        return 400, {"ok": False, "error": str(exc)}
    return 200, {"ok": True, "batch": batch.to_public_dict(include_records=True)}


def _handle_reveal(body: Mapping[str, Any], *, table: ConfidentialSealedBidTable | None) -> ResponseT:
    if table is None:
        return 503, {"ok": False, "error": "confidential_sealed_bid_table_unavailable"}
    unknown = _reject_unknown_fields(
        body,
        allowed={"batch_id", "bidder_id", "quantity", "limit_price", "nonce"},
    )
    if unknown is not None:
        return unknown
    try:
        nonce = body.get("nonce")
        if not isinstance(nonce, str) or not nonce:
            raise ValueError("bad_nonce")
        batch, record = table.reveal(
            batch_id=_request_id(body, name="batch_id", default=DEFAULT_BATCH_ID),
            bidder_id=_request_id(body, name="bidder_id"),
            quantity=_request_int(body, name="quantity", lo=1, hi=MAX_UNITS),
            limit_price=_request_int(body, name="limit_price", lo=1, hi=MAX_PRICE),
            nonce=nonce,
        )
    except Exception as exc:
        return 400, {"ok": False, "error": str(exc)}
    return 200, {
        "ok": True,
        "batch": batch.to_public_dict(include_records=False),
        "reveal": record.to_public_dict(),
        "nonce_persisted": False,
    }


def _handle_settle(
    body: Mapping[str, Any],
    *,
    table: ConfidentialSealedBidTable | None,
) -> ResponseT:
    if table is None:
        return 503, {"ok": False, "error": "confidential_sealed_bid_table_unavailable"}
    unknown = _reject_unknown_fields(body, allowed={"batch_id"})
    if unknown is not None:
        return unknown
    try:
        batch_id = _request_id(body, name="batch_id", default=DEFAULT_BATCH_ID)
        batch = table.settle(batch_id=batch_id)
    except Exception as exc:
        return 400, {"ok": False, "error": str(exc)}
    return 200, {
        "ok": True,
        "batch": batch.to_public_dict(include_records=True),
        "settlement": batch.settlement,
        "bond_outcome": batch.bond_outcome,
        "asset_settlement": None,
        "asset_settlement_executed": False,
    }


def handle_confidential_sealed_bid_request(
    method: str,
    path: str,
    raw_body: Optional[bytes],
    *,
    table: ConfidentialSealedBidTable | None = None,
) -> ResponseT:
    if method == "GET" and path == "/api/confidential/sealed-bid/status":
        return _status_payload(table)

    handlers = {
        "/api/confidential/sealed-bid/reset": _handle_reset,
        "/api/confidential/sealed-bid/commit": _handle_commit,
        "/api/confidential/sealed-bid/open-reveal": _handle_open_reveal,
        "/api/confidential/sealed-bid/reveal": _handle_reveal,
        "/api/confidential/sealed-bid/settle": _handle_settle,
    }
    handler = handlers.get(path)
    if handler is None:
        return 404, {"ok": False, "error": "not_found"}
    if method != "POST":
        return 405, {"ok": False, "error": "method_not_allowed"}
    obj, err = _parse_json_body(raw_body)
    if err is not None or obj is None:
        return 400, {"ok": False, "error": str(err or "invalid_request")}
    if path == "/api/confidential/sealed-bid/settle":
        return _handle_settle(obj, table=table)
    return handler(obj, table=table)
