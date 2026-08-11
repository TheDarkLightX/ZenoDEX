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

import hashlib
import json
import os
import re
import tempfile
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable, Mapping, Optional, Tuple

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
from ..state.canonical import canonical_hex_fixed_allow_0x, canonical_json_bytes, domain_sep_bytes, sha256_hex


MAX_POST_BODY = 96_000
MAX_BATCHES = 128
MAX_COMMITS_PER_BATCH = 512
DEFAULT_BATCH_ID = "local-sealed-bid-v1"
DEFAULT_UNITS_FOR_SALE = 10
DEFAULT_COMMIT_EPOCH = 1
DEFAULT_REVEAL_DEADLINE_EPOCH = 2
DEFAULT_BOND_AMOUNT = 5
DEFAULT_LOCAL_PAYMENT_ASSET = "0x" + "44" * 32
DEFAULT_LOCAL_INVENTORY_ASSET = "0x" + "55" * 32

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


def _env_float(name: str, default: float, *, lo: float, hi: float) -> float:
    raw = os.environ.get(name)
    if raw is None or not raw.strip():
        return float(default)
    try:
        value = float(raw.strip())
    except Exception:
        return float(default)
    return min(max(value, lo), hi)


def _env_int(name: str, default: int, *, lo: int, hi: int) -> int:
    raw = os.environ.get(name)
    if raw is None or not raw.strip():
        return int(default)
    try:
        value = int(raw.strip())
    except Exception:
        return int(default)
    return min(max(value, lo), hi)


def _hash_payload(domain: str, payload: Mapping[str, Any]) -> str:
    return sha256_hex(domain_sep_bytes(domain) + canonical_json_bytes(dict(payload)))


def _return_signed_tau_tx_payloads() -> bool:
    return _env_bool("CONFIDENTIAL_SEALED_BID_RETURN_SIGNED_TAU_TX_PAYLOAD", False)


def _is_local_chain_id(chain_id: str) -> bool:
    text = str(chain_id).strip().lower()
    return text in {"local", "localtest", "local-testnet", "tau-local"} or text.startswith(("local-", "tau-local-"))


def _fixture_settlement_allowed(chain_id: str) -> bool:
    return _is_local_chain_id(chain_id) or _env_bool("CONFIDENTIAL_SEALED_BID_ALLOW_FIXTURE_SETTLEMENT", False)


def _redacted_tau_tx_payload(payload: Mapping[str, Any] | None) -> Mapping[str, Any] | None:
    if payload is None:
        return None
    if _return_signed_tau_tx_payloads():
        return dict(payload)
    raw_operations = payload.get("operations")
    operation_streams = sorted(str(key) for key in raw_operations.keys()) if isinstance(raw_operations, Mapping) else []
    return {
        "redacted": True,
        "redaction_reason": "signed_tau_tx_payload_response_redaction",
        "payload_hash": _hash_payload("zenodex.confidential_sealed_bid.tau_tx_payload/v1", payload),
        "sender_pubkey": payload.get("sender_pubkey"),
        "sequence_number": payload.get("sequence_number"),
        "expiration_time": payload.get("expiration_time"),
        "fee_limit": str(payload.get("fee_limit")),
        "operation_streams": operation_streams,
    }


def _redacted_operations(operations: Mapping[str, Any] | None) -> Mapping[str, Any] | None:
    if operations is None:
        return None
    if _return_signed_tau_tx_payloads():
        return dict(operations)
    stream13 = operations.get("13")
    settlement_ids: list[str] = []
    batch_ids: list[str] = []
    if isinstance(stream13, list):
        for item in stream13:
            if not isinstance(item, Mapping):
                continue
            settlement_id = item.get("settlement_id")
            batch_id = item.get("batch_id")
            if isinstance(settlement_id, str):
                settlement_ids.append(settlement_id)
            if isinstance(batch_id, str):
                batch_ids.append(batch_id)
    return {
        "redacted": True,
        "redaction_reason": "authority_operation_response_redaction",
        "operations_hash": _hash_payload("zenodex.confidential_sealed_bid.operations/v1", operations),
        "operation_streams": sorted(str(key) for key in operations.keys()),
        "stream13_settlement_ids": sorted(set(settlement_ids)),
        "stream13_batch_ids": sorted(set(batch_ids)),
    }


def _redact_response_authority_material(payload: dict[str, Any]) -> dict[str, Any]:
    report = payload.get("report")
    if isinstance(report, dict):
        if isinstance(report.get("operations"), Mapping):
            report["operations"] = _redacted_operations(report.get("operations"))
        if isinstance(report.get("tau_tx_payload"), Mapping):
            report["tau_tx_payload"] = _redacted_tau_tx_payload(report.get("tau_tx_payload"))
    return payload


def _request_bool(body: Mapping[str, Any], *, name: str, default: bool) -> bool:
    value = body.get(name, default)
    if isinstance(value, bool):
        return bool(value)
    if isinstance(value, str):
        text = value.strip().lower()
        if text in {"1", "true", "yes", "on"}:
            return True
        if text in {"0", "false", "no", "off"}:
            return False
    raise ValueError(f"bad_{name}")


def _canonical_pubkey(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    return canonical_hex_fixed_allow_0x(value, nbytes=48, name=name)


def _canonical_asset(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    return canonical_hex_fixed_allow_0x(value, nbytes=32, name=name)


def _pubkey_for_rpc(value: str) -> str:
    s = value.strip().lower()
    return s[2:] if s.startswith("0x") else s


def _default_fixture_privkeys() -> dict[str, str]:
    return {
        "seller": "0x" + "01".rjust(64, "0"),
        "alice": "0x" + "02".rjust(64, "0"),
        "bob": "0x" + "03".rjust(64, "0"),
        "carol": "0x" + "04".rjust(64, "0"),
    }


def _privkey_pubkey(privkey: object) -> str:
    from .tau_net_client import bls_pubkey_hex_from_privkey

    if not isinstance(privkey, (str, int, bytes, bytearray)):
        raise ValueError("privkey must be string, int, or bytes")
    return "0x" + bls_pubkey_hex_from_privkey(privkey)


def _sign_asset_authorization(body: Mapping[str, Any], *, privkey: object) -> str:
    from py_ecc.bls import G2Basic

    from .tau_net_client import _parse_privkey_to_int
    from .tau_testnet_dex_plugin import confidential_sealed_bid_asset_authorization_message_v1

    digest = hashlib.sha256(confidential_sealed_bid_asset_authorization_message_v1(body)).digest()
    return "0x" + G2Basic.Sign(_parse_privkey_to_int(privkey), digest).hex()


def _asset_settlement_nonce_key(seller_pubkey: str) -> str:
    payload = b"zenodex:confidential_sealed_bid_settlement_nonce:v1\x00" + seller_pubkey.encode("ascii")
    return "0x" + hashlib.sha384(payload).hexdigest()


def _dex_state_view(app_state: Mapping[str, Any]) -> Mapping[str, Any]:
    dex_state = app_state.get("dex_state")
    if isinstance(dex_state, Mapping):
        return dex_state
    return app_state


def _balance_for_asset(app_state: Mapping[str, Any], *, pubkey: str, asset_id: str) -> int:
    raw = _dex_state_view(app_state).get("balances") or []
    if not isinstance(raw, list):
        return 0
    target_pubkey = pubkey.strip().lower()
    target_asset = asset_id.strip().lower()
    for entry in raw:
        if not isinstance(entry, Mapping):
            continue
        if str(entry.get("pubkey", "")).strip().lower() != target_pubkey:
            continue
        if str(entry.get("asset", "")).strip().lower() != target_asset:
            continue
        amount = entry.get("amount")
        return int(amount) if isinstance(amount, int) and not isinstance(amount, bool) else 0
    return 0


def _last_asset_settlement_nonce(app_state: Mapping[str, Any], *, seller_pubkey: str) -> int:
    raw = _dex_state_view(app_state).get("nonces") or []
    if not isinstance(raw, list):
        return 0
    target = _asset_settlement_nonce_key(seller_pubkey).lower()
    for entry in raw:
        if not isinstance(entry, Mapping):
            continue
        if str(entry.get("pubkey", "")).strip().lower() == target:
            last = entry.get("last_nonce")
            return int(last) if isinstance(last, int) and not isinstance(last, bool) and last >= 0 else 0
    return 0


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
    asset_settlement: dict[str, Any] | None = None

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
            "asset_settlement": self.asset_settlement,
            "asset_settlement_executed": bool(
                isinstance(self.asset_settlement, Mapping)
                and self.asset_settlement.get("ok") is True
            ),
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
            "asset_settlement": self.asset_settlement,
        }

    @classmethod
    def from_json(cls, obj: Mapping[str, Any]) -> "SealedBidBatch":
        commits_obj = obj.get("commits")
        reveals_obj = obj.get("reveals")
        if not isinstance(commits_obj, Mapping) or not isinstance(reveals_obj, Mapping):
            raise ValueError("bad_batch_records")
        batch = cls(
            batch_id=str(obj["batch_id"]),
            units_for_sale=int(obj["units_for_sale"]),
            commit_epoch=int(obj["commit_epoch"]),
            reveal_deadline_epoch=int(obj["reveal_deadline_epoch"]),
            default_bond_amount=int(obj["default_bond_amount"]),
            phase=str(obj["phase"]),
            settlement=dict(obj["settlement"]) if isinstance(obj.get("settlement"), Mapping) else None,
            bond_outcome=dict(obj["bond_outcome"]) if isinstance(obj.get("bond_outcome"), Mapping) else None,
            asset_settlement=dict(obj["asset_settlement"]) if isinstance(obj.get("asset_settlement"), Mapping) else None,
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
        asset_settlement: Mapping[str, Any] | None = None,
    ) -> SealedBidBatch:
        batch = self._get_batch(batch_id)
        if batch is None:
            raise ValueError("unknown_batch")
        batch.settlement = dict(settlement)
        batch.bond_outcome = dict(bond_outcome)
        if asset_settlement is not None:
            batch.asset_settlement = dict(asset_settlement)
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


AssetSettlementSubmitter = Callable[
    [SealedBidBatch, Mapping[str, Any], Mapping[str, Any], Mapping[str, Any]],
    Mapping[str, Any],
]


def _local_ledger_tau_client():
    from .tau_net_client import TauNetTcpClient, TauNetTcpConfig

    return TauNetTcpClient(
        TauNetTcpConfig(
            host=_env_str(
                "CONFIDENTIAL_SEALED_BID_TAU_HOST",
                _env_str("PERPS_WALLET_TAU_HOST", _env_str("ZUSD_MONETARY_WALLET_TAU_HOST", "127.0.0.1")),
            ),
            port=_env_int(
                "CONFIDENTIAL_SEALED_BID_TAU_PORT",
                _env_int(
                    "PERPS_WALLET_TAU_PORT",
                    _env_int("ZUSD_MONETARY_WALLET_TAU_PORT", 65432, lo=1, hi=65535),
                    lo=1,
                    hi=65535,
                ),
                lo=1,
                hi=65535,
            ),
            timeout_s=_env_float(
                "CONFIDENTIAL_SEALED_BID_TAU_TIMEOUT_S",
                _env_float(
                    "PERPS_WALLET_TAU_TIMEOUT_S",
                    _env_float("ZUSD_MONETARY_WALLET_TAU_TIMEOUT_S", 3.0, lo=0.1, hi=60.0),
                    lo=0.1,
                    hi=60.0,
                ),
                lo=0.1,
                hi=60.0,
            ),
        )
    )


def _load_app_state(client: Any) -> tuple[dict[str, Any], str | None]:
    raw = client.getappstate(full=True).strip()
    obj = json.loads(raw)
    if not isinstance(obj, dict):
        raise ValueError("invalid getappstate response")
    app_state = obj.get("app_state")
    if app_state is None:
        app_state = {}
    if not isinstance(app_state, dict):
        raise ValueError("invalid app_state payload")
    app_hash = obj.get("app_hash")
    return app_state, str(app_hash) if isinstance(app_hash, str) and app_hash else None


def _auto_mine_enabled() -> bool:
    return _env_bool(
        "CONFIDENTIAL_SEALED_BID_AUTO_MINE",
        _env_bool("PERPS_WALLET_AUTO_MINE", _env_bool("ZUSD_MONETARY_WALLET_AUTO_MINE", False)),
    )


def _wait_for_app_hash_change(client: Any, app_hash_before: str | None) -> tuple[dict[str, Any], str | None]:
    timeout = _env_float("CONFIDENTIAL_SEALED_BID_APP_HASH_WAIT_S", 2.0, lo=0.0, hi=30.0)
    deadline = time.monotonic() + timeout
    last_state: dict[str, Any] = {}
    last_hash: str | None = None
    while True:
        state, observed_hash = _load_app_state(client)
        last_state = state
        last_hash = observed_hash
        if observed_hash is not None and (app_hash_before is None or observed_hash != app_hash_before):
            return state, observed_hash
        if time.monotonic() >= deadline:
            return last_state, last_hash
        time.sleep(0.25)


def submit_confidential_sealed_bid_local_ledger_settlement(
    batch: SealedBidBatch,
    asset_request: Mapping[str, Any],
    settlement: Mapping[str, Any],
    _bond_outcome: Mapping[str, Any],
) -> Mapping[str, Any]:
    """Submit a local-testnet stream-13 asset settlement transaction."""

    from .tau_net_client import (
        build_signed_tau_transaction,
        tau_rpc_invalid_sequence_numbers,
        tau_rpc_response_is_success,
    )
    from .tau_testnet_dex_plugin import (
        _confidential_sealed_bid_asset_authorization_body_v1,
        _confidential_sealed_bid_fills_hash,
    )

    request = dict(asset_request)
    mode = str(request.get("mode", "local_ledger")).strip()
    if mode not in {"local_ledger", "local_ledger_fixture"}:
        raise ValueError("unsupported_asset_settlement_mode")
    chain_id = str(
        request.get("chain_id")
        or _env_str("CONFIDENTIAL_SEALED_BID_CHAIN_ID", _env_str("TAU_DEX_CHAIN_ID", "tau-local"))
    )
    if mode == "local_ledger_fixture" and not _fixture_settlement_allowed(chain_id):
        raise ValueError("confidential_sealed_bid_fixture_settlement_not_allowed")
    payment_asset = _canonical_asset(
        request.get("payment_asset", DEFAULT_LOCAL_PAYMENT_ASSET),
        name="asset_settlement.payment_asset",
    )
    inventory_asset = _canonical_asset(
        request.get("inventory_asset", DEFAULT_LOCAL_INVENTORY_ASSET),
        name="asset_settlement.inventory_asset",
    )
    if payment_asset == inventory_asset:
        raise ValueError("asset_settlement_assets_must_differ")

    fixture_privkeys = _default_fixture_privkeys()
    buyer_privkeys_raw = request.get("buyer_privkeys")
    buyer_privkeys = dict(buyer_privkeys_raw) if isinstance(buyer_privkeys_raw, Mapping) else {}
    if mode == "local_ledger_fixture":
        seller_privkey: object = request.get("seller_privkey", fixture_privkeys["seller"])
        for role, privkey in fixture_privkeys.items():
            if role != "seller":
                buyer_privkeys.setdefault(role, privkey)
    else:
        seller_privkey = request.get("seller_privkey")
        if seller_privkey is None:
            raise ValueError("missing_seller_privkey")
        if not buyer_privkeys:
            raise ValueError("missing_buyer_privkeys")

    seller_pubkey = _canonical_pubkey(_privkey_pubkey(seller_privkey), name="seller_pubkey")
    fills_raw = settlement.get("fills")
    if not isinstance(fills_raw, list):
        raise ValueError("settlement_fills_malformed")
    if not fills_raw:
        return {
            "ok": True,
            "asset_settlement_executed": False,
            "mode": mode,
            "reason": "no_filled_bids",
            "testnet_only": mode == "local_ledger_fixture",
            "production_security_claim": False,
        }

    clearing_price = int(settlement.get("clearing_price", 0))
    if clearing_price <= 0:
        raise ValueError("bad_clearing_price")

    fills: list[dict[str, Any]] = []
    for index, fill_obj in enumerate(fills_raw):
        if not isinstance(fill_obj, Mapping):
            raise ValueError(f"settlement.fills[{index}] must be an object")
        bidder_id = str(fill_obj.get("bidder_id", "")).strip()
        if not bidder_id:
            raise ValueError(f"settlement.fills[{index}].bidder_id missing")
        buyer_privkey = buyer_privkeys.get(bidder_id)
        if buyer_privkey is None:
            raise ValueError(f"missing_buyer_privkey:{bidder_id}")
        bidder_pubkey = _canonical_pubkey(_privkey_pubkey(buyer_privkey), name=f"buyer_pubkey[{bidder_id}]")
        fills.append(
            {
                "bidder_id": bidder_id,
                "bidder_pubkey": bidder_pubkey,
                "commitment": str(fill_obj.get("commitment", "")),
                "filled_quantity": int(fill_obj.get("filled_quantity", 0)),
                "paid_price": int(fill_obj.get("paid_price", 0)),
                "_buyer_privkey": buyer_privkey,
            }
        )

    fills_hash = _confidential_sealed_bid_fills_hash(fills)
    total_quantity = sum(int(fill["filled_quantity"]) for fill in fills)
    total_payment = sum(int(fill["filled_quantity"]) * int(fill["paid_price"]) for fill in fills)
    settlement_id = str(request.get("settlement_id") or f"{batch.batch_id}:asset-settlement:v1")

    seller_body = _confidential_sealed_bid_asset_authorization_body_v1(
        chain_id=chain_id,
        settlement_id=settlement_id,
        batch_id=batch.batch_id,
        role="seller_inventory",
        pubkey=seller_pubkey,
        payment_asset=payment_asset,
        inventory_asset=inventory_asset,
        clearing_price=clearing_price,
        quantity=total_quantity,
        amount=0,
        fills_hash=fills_hash,
    )
    op_fills: list[dict[str, Any]] = []
    for fill in fills:
        buyer_body = _confidential_sealed_bid_asset_authorization_body_v1(
            chain_id=chain_id,
            settlement_id=settlement_id,
            batch_id=batch.batch_id,
            role="buyer_payment",
            pubkey=str(fill["bidder_pubkey"]),
            payment_asset=payment_asset,
            inventory_asset=inventory_asset,
            clearing_price=clearing_price,
            quantity=int(fill["filled_quantity"]),
            amount=int(fill["filled_quantity"]) * int(fill["paid_price"]),
            fills_hash=fills_hash,
            commitment=str(fill["commitment"]),
        )
        op_fills.append(
            {
                "bidder_id": str(fill["bidder_id"]),
                "bidder_pubkey": str(fill["bidder_pubkey"]),
                "commitment": str(fill["commitment"]),
                "filled_quantity": int(fill["filled_quantity"]),
                "paid_price": int(fill["paid_price"]),
                "buyer_payment_signature": _sign_asset_authorization(
                    buyer_body,
                    privkey=fill["_buyer_privkey"],
                ),
            }
        )

    client = _local_ledger_tau_client()
    app_state_before, app_hash_before = _load_app_state(client)
    settlement_nonce = _last_asset_settlement_nonce(app_state_before, seller_pubkey=seller_pubkey) + 1
    op = {
        "module": "ZenoConfidentialSealedBid",
        "version": "1",
        "action": "settle_assets",
        "settlement_id": settlement_id,
        "batch_id": batch.batch_id,
        "seller_pubkey": seller_pubkey,
        "payment_asset": payment_asset,
        "inventory_asset": inventory_asset,
        "units_for_sale": int(batch.units_for_sale),
        "clearing_price": clearing_price,
        "nonce": settlement_nonce,
        "seller_inventory_signature": _sign_asset_authorization(seller_body, privkey=seller_privkey),
        "fills": op_fills,
    }
    operations: dict[str, Any] = {"13": [op]}
    fund_local_fixture = _request_bool(
        request,
        name="fund_local_fixture",
        default=(mode == "local_ledger_fixture"),
    )
    if fund_local_fixture and not _fixture_settlement_allowed(chain_id):
        raise ValueError("confidential_sealed_bid_fixture_funding_not_allowed")
    if fund_local_fixture:
        mint_rows = [{"pubkey": seller_pubkey, "asset": inventory_asset, "amount": total_quantity}]
        for fill in fills:
            mint_rows.append(
                {
                    "pubkey": str(fill["bidder_pubkey"]),
                    "asset": payment_asset,
                    "amount": int(fill["filled_quantity"]) * int(fill["paid_price"]),
                }
            )
        operations["7"] = {"mint": mint_rows}

    signer_privkey = request.get("tx_signer_privkey", seller_privkey)
    signer_pubkey = _canonical_pubkey(_privkey_pubkey(signer_privkey), name="tx_signer_pubkey")
    tx_sequence_number = int(client.get_sequence(_pubkey_for_rpc(signer_pubkey)))
    tx_fee_limit = _request_int(request, name="tx_fee_limit", default=0, lo=0, hi=10**30)
    deadline = _request_int(
        request,
        name="deadline",
        default=int(time.time()) + _env_int("CONFIDENTIAL_SEALED_BID_DEFAULT_DEADLINE_S", 3600, lo=1, hi=86_400),
        lo=0,
        hi=2**63 - 1,
    )
    tau_tx_payload = build_signed_tau_transaction(
        privkey=signer_privkey,
        sequence_number=tx_sequence_number,
        expiration_time=deadline,
        operations=operations,
        fee_limit=tx_fee_limit,
    )
    send_resp = client.sendtx(tau_tx_payload)
    submission: dict[str, Any] = {"sendtx_response": send_resp}
    if not tau_rpc_response_is_success(send_resp):
        invalid_sequence = tau_rpc_invalid_sequence_numbers(send_resp)
        if invalid_sequence is not None and int(invalid_sequence[1]) == int(tx_sequence_number):
            tx_sequence_number = int(invalid_sequence[0])
            submission["retry_sequence_error"] = {
                "expected": int(invalid_sequence[0]),
                "got": int(invalid_sequence[1]),
            }
            tau_tx_payload = build_signed_tau_transaction(
                privkey=signer_privkey,
                sequence_number=tx_sequence_number,
                expiration_time=deadline,
                operations=operations,
                fee_limit=tx_fee_limit,
            )
            send_resp = client.sendtx(tau_tx_payload)
            submission["retry_sendtx_response"] = send_resp
        if not tau_rpc_response_is_success(send_resp):
            return {"ok": False, "error": "sendtx_failed", "submission": submission}

    if _auto_mine_enabled():
        createblock_resp = client.createblock()
        submission["createblock_response"] = createblock_resp
        if not tau_rpc_response_is_success(createblock_resp):
            _observed_state, observed_hash = _wait_for_app_hash_change(client, app_hash_before)
            submission["observed_app_hash_after_createblock"] = observed_hash
            if observed_hash == app_hash_before:
                return {"ok": False, "error": "createblock_failed", "submission": submission}

    app_state_after, app_hash_after = _load_app_state(client)
    balances_after = {
        "seller_inventory": _balance_for_asset(app_state_after, pubkey=seller_pubkey, asset_id=inventory_asset),
        "seller_payment": _balance_for_asset(app_state_after, pubkey=seller_pubkey, asset_id=payment_asset),
    }
    for fill in fills:
        bidder_id = str(fill["bidder_id"])
        bidder_pubkey = str(fill["bidder_pubkey"])
        balances_after[f"{bidder_id}_payment"] = _balance_for_asset(
            app_state_after,
            pubkey=bidder_pubkey,
            asset_id=payment_asset,
        )
        balances_after[f"{bidder_id}_inventory"] = _balance_for_asset(
            app_state_after,
            pubkey=bidder_pubkey,
            asset_id=inventory_asset,
        )

    return _redact_response_authority_material({
        "ok": True,
        "asset_settlement_executed": True,
        "mode": mode,
        "testnet_only": mode == "local_ledger_fixture",
        "production_security_claim": False,
        "chain_id": chain_id,
        "stream_key": "13",
        "fund_local_fixture": fund_local_fixture,
        "settlement_id": settlement_id,
        "seller_pubkey": seller_pubkey,
        "payment_asset": payment_asset,
        "inventory_asset": inventory_asset,
        "total_quantity": total_quantity,
        "total_payment": total_payment,
        "settlement_nonce": settlement_nonce,
        "app_hash_before": app_hash_before,
        "app_hash_after": app_hash_after,
        "balances_after": balances_after,
        "submission": submission,
        "report": {
            "operations": operations,
            "tau_tx_payload": tau_tx_payload,
        },
    })


def _status_payload(
    table: ConfidentialSealedBidTable | None,
    *,
    asset_settlement_submitter: AssetSettlementSubmitter | None = None,
) -> ResponseT:
    if table is None:
        return 503, {"ok": False, "error": "confidential_sealed_bid_table_unavailable"}
    status = table.status()
    status["asset_settlement_available"] = asset_settlement_submitter is not None
    status["local_testnet_scope"] = {
        "asset_settlement": asset_settlement_submitter is not None,
        "asset_settlement_mode": "local_ledger_stream_13" if asset_settlement_submitter is not None else "unavailable",
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
    asset_settlement_submitter: AssetSettlementSubmitter | None = None,
) -> ResponseT:
    if table is None:
        return 503, {"ok": False, "error": "confidential_sealed_bid_table_unavailable"}
    unknown = _reject_unknown_fields(body, allowed={"batch_id", "asset_settlement"})
    if unknown is not None:
        return unknown
    try:
        batch_id = _request_id(body, name="batch_id", default=DEFAULT_BATCH_ID)
        asset_request_obj = body.get("asset_settlement")
        if asset_request_obj is None:
            batch = table.settle(batch_id=batch_id)
        else:
            if not isinstance(asset_request_obj, Mapping):
                return 400, {"ok": False, "error": "bad_asset_settlement"}
            if asset_settlement_submitter is None:
                return 503, {"ok": False, "error": "asset_settlement_submitter_unavailable"}
            batch, settlement, bond_outcome = table.settlement_preview(batch_id=batch_id)
            if (
                batch.phase == "settled"
                and isinstance(batch.asset_settlement, Mapping)
                and batch.asset_settlement.get("ok") is True
            ):
                return 200, {
                    "ok": True,
                    "batch": batch.to_public_dict(include_records=True),
                    "settlement": batch.settlement,
                    "bond_outcome": batch.bond_outcome,
                    "asset_settlement": batch.asset_settlement,
                    "asset_settlement_executed": bool(batch.asset_settlement.get("asset_settlement_executed")),
                }
            asset_settlement = asset_settlement_submitter(
                batch,
                asset_request_obj,
                settlement,
                bond_outcome,
            )
            if not isinstance(asset_settlement, Mapping) or asset_settlement.get("ok") is not True:
                return 502, {
                    "ok": False,
                    "error": "asset_settlement_failed",
                    "asset_settlement": dict(asset_settlement) if isinstance(asset_settlement, Mapping) else None,
                }
            batch = table.record_settlement(
                batch_id=batch_id,
                settlement=settlement,
                bond_outcome=bond_outcome,
                asset_settlement=asset_settlement,
            )
    except Exception as exc:
        return 400, {"ok": False, "error": str(exc)}
    return 200, {
        "ok": True,
        "batch": batch.to_public_dict(include_records=True),
        "settlement": batch.settlement,
        "bond_outcome": batch.bond_outcome,
        "asset_settlement": batch.asset_settlement,
        "asset_settlement_executed": bool(
            isinstance(batch.asset_settlement, Mapping)
            and batch.asset_settlement.get("asset_settlement_executed") is True
        ),
    }


def handle_confidential_sealed_bid_request(
    method: str,
    path: str,
    raw_body: Optional[bytes],
    *,
    table: ConfidentialSealedBidTable | None = None,
    asset_settlement_submitter: AssetSettlementSubmitter | None = None,
) -> ResponseT:
    if method == "GET" and path == "/api/confidential/sealed-bid/status":
        return _status_payload(table, asset_settlement_submitter=asset_settlement_submitter)

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
        return _handle_settle(
            obj,
            table=table,
            asset_settlement_submitter=asset_settlement_submitter,
        )
    return handler(obj, table=table)
