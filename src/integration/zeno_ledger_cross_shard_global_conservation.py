"""Global cross-shard conservation receipt for ZenoLedger artifacts."""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from typing import Any, Mapping

from src.integration.zeno_ledger_cross_shard_effect_application import (
    CrossShardAppliedEffectsStateV0,
    validate_cross_shard_ledger_effects_artifact_v0,
)
from src.integration.zeno_ledger_tau_export import (
    validate_cross_shard_posting_summary_export_v0,
)
from src.integration.zeno_ledger_v0 import ROOT_NBYTES, hash_v0
from src.state.canonical import canonical_hex_fixed_allow_0x

CROSS_SHARD_GLOBAL_CONSERVATION_RECEIPT_SCHEMA_V0 = (
    "zenodex/zeno_ledger/cross_shard_global_conservation_receipt/v0"
)

_RECEIPT_KEYS_V0 = frozenset(
    {
        "schema",
        "status",
        "sharded_settlement_certificate_hash",
        "posting_summary_hash",
        "ledger_effects_hash",
        "pre_replay_state_root",
        "post_replay_state_root",
        "effect_count",
        "total_debit_atoms",
        "total_credit_atoms",
        "asset_rows",
        "receipt_hash",
    }
)
_ASSET_ROW_KEYS_V0 = frozenset(
    {
        "asset_id",
        "posting_debit_atoms",
        "posting_credit_atoms",
        "effect_debit_atoms",
        "effect_credit_atoms",
    }
)


CrossShardGlobalConservationReceiptV0 = dict[str, Any]


@dataclass(frozen=True)
class CrossShardGlobalConservationReceiptVerdict:
    ok: bool
    error: str | None
    receipt: CrossShardGlobalConservationReceiptV0 | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.ok, bool):
            raise TypeError("ok must be bool")
        if self.ok:
            if self.error is not None:
                raise ValueError("accepted conservation receipt verdict cannot include error")
            if not isinstance(self.receipt, dict):
                raise TypeError("accepted conservation receipt verdict requires receipt")
            return
        if not isinstance(self.error, str) or not self.error:
            raise ValueError("rejected conservation receipt verdict requires error")
        if self.receipt is not None:
            raise ValueError("rejected conservation receipt verdict cannot include receipt")


def build_cross_shard_global_conservation_receipt_v0(
    *,
    posting_summary: Mapping[str, Any],
    effects_artifact: Mapping[str, Any],
    pre_replay_state: CrossShardAppliedEffectsStateV0,
    post_replay_state: CrossShardAppliedEffectsStateV0,
    sharded_settlement_certificate_hash: str | None = None,
) -> CrossShardGlobalConservationReceiptV0:
    """Build a receipt tying cross-shard summaries, effects, and replay roots.

    Preconditions: inputs are already local artifacts. The function still
    validates each one and fails closed on any mismatch.

    Preserved invariant:
    `post_replay_state = pre_replay_state + ledger_effects_hash`.
    """

    if not isinstance(pre_replay_state, CrossShardAppliedEffectsStateV0):
        raise TypeError("pre_replay_state must be CrossShardAppliedEffectsStateV0")
    if not isinstance(post_replay_state, CrossShardAppliedEffectsStateV0):
        raise TypeError("post_replay_state must be CrossShardAppliedEffectsStateV0")
    posting = validate_cross_shard_posting_summary_export_v0(posting_summary)
    artifact = validate_cross_shard_ledger_effects_artifact_v0(effects_artifact)
    posting_hash = str(posting["posting_summary_hash"])
    posting_settlement_hash = _require_hash(
        posting.get("sharded_settlement_certificate_hash"),
        name="posting.sharded_settlement_certificate_hash",
    )
    if sharded_settlement_certificate_hash is None:
        settlement_hash = posting_settlement_hash
    else:
        settlement_hash = _require_hash(
            sharded_settlement_certificate_hash,
            name="sharded_settlement_certificate_hash",
        )
        if settlement_hash != posting_settlement_hash:
            raise ValueError("receipt settlement hash does not match posting summary source")
    ledger_effects_hash = str(artifact["ledger_effects_hash"])
    if artifact["source_posting_summary_hash"] != posting_hash:
        raise ValueError("cross-shard effects are not sourced from posting summary")
    if pre_replay_state.contains(ledger_effects_hash):
        raise ValueError("cross-shard ledger effects already present in pre replay state")
    expected_post = pre_replay_state.add(ledger_effects_hash)
    if post_replay_state != expected_post:
        raise ValueError("post replay state must equal pre replay state plus ledger effects hash")

    asset_rows = _asset_rows_from_posting_and_effects(
        posting=posting,
        artifact=artifact,
    )
    total_debit = _require_non_negative_int(
        artifact["total_debit_atoms"],
        name="cross_shard_ledger_effects.total_debit_atoms",
    )
    total_credit = _require_non_negative_int(
        artifact["total_credit_atoms"],
        name="cross_shard_ledger_effects.total_credit_atoms",
    )
    if total_debit != total_credit:
        raise ValueError("cross-shard global conservation totals must balance")

    body: CrossShardGlobalConservationReceiptV0 = {
        "schema": CROSS_SHARD_GLOBAL_CONSERVATION_RECEIPT_SCHEMA_V0,
        "status": "verified_global_conservation",
        "sharded_settlement_certificate_hash": settlement_hash,
        "posting_summary_hash": posting_hash,
        "ledger_effects_hash": ledger_effects_hash,
        "pre_replay_state_root": pre_replay_state.root_hash(),
        "post_replay_state_root": post_replay_state.root_hash(),
        "effect_count": _require_non_negative_int(
            artifact["effect_count"],
            name="cross_shard_ledger_effects.effect_count",
        ),
        "total_debit_atoms": total_debit,
        "total_credit_atoms": total_credit,
        "asset_rows": asset_rows,
    }
    return {
        **body,
        "receipt_hash": hash_v0(
            "cross_shard_global_conservation_receipt_v0",
            body,
        ),
    }


def validate_cross_shard_global_conservation_receipt_v0(
    receipt: Mapping[str, Any],
) -> CrossShardGlobalConservationReceiptV0:
    obj = _require_mapping(receipt, name="cross_shard_global_conservation_receipt")
    _reject_unknown_keys(
        obj,
        allowed=_RECEIPT_KEYS_V0,
        name="cross_shard_global_conservation_receipt",
    )
    if obj.get("schema") != CROSS_SHARD_GLOBAL_CONSERVATION_RECEIPT_SCHEMA_V0:
        raise ValueError("cross-shard global conservation receipt schema mismatch")
    if obj.get("status") != "verified_global_conservation":
        raise ValueError("cross-shard global conservation receipt status mismatch")
    settlement_hash = obj.get("sharded_settlement_certificate_hash")
    if settlement_hash is not None:
        _require_hash(settlement_hash, name="receipt.sharded_settlement_certificate_hash")
    _require_hash(obj.get("posting_summary_hash"), name="receipt.posting_summary_hash")
    _require_hash(obj.get("ledger_effects_hash"), name="receipt.ledger_effects_hash")
    _require_hash(obj.get("pre_replay_state_root"), name="receipt.pre_replay_state_root")
    _require_hash(obj.get("post_replay_state_root"), name="receipt.post_replay_state_root")
    effect_count = _require_non_negative_int(
        obj.get("effect_count"),
        name="receipt.effect_count",
    )
    total_debit = _require_non_negative_int(
        obj.get("total_debit_atoms"),
        name="receipt.total_debit_atoms",
    )
    total_credit = _require_non_negative_int(
        obj.get("total_credit_atoms"),
        name="receipt.total_credit_atoms",
    )
    if total_debit != total_credit:
        raise ValueError("cross-shard global conservation receipt totals must balance")
    rows = _parse_asset_rows(obj.get("asset_rows"))
    if sum(row["effect_debit_atoms"] for row in rows) != total_debit:
        raise ValueError("receipt asset row debit total mismatch")
    if sum(row["effect_credit_atoms"] for row in rows) != total_credit:
        raise ValueError("receipt asset row credit total mismatch")
    body: CrossShardGlobalConservationReceiptV0 = {
        "schema": CROSS_SHARD_GLOBAL_CONSERVATION_RECEIPT_SCHEMA_V0,
        "status": "verified_global_conservation",
        "sharded_settlement_certificate_hash": settlement_hash,
        "posting_summary_hash": obj["posting_summary_hash"],
        "ledger_effects_hash": obj["ledger_effects_hash"],
        "pre_replay_state_root": obj["pre_replay_state_root"],
        "post_replay_state_root": obj["post_replay_state_root"],
        "effect_count": effect_count,
        "total_debit_atoms": total_debit,
        "total_credit_atoms": total_credit,
        "asset_rows": rows,
    }
    expected = {
        **body,
        "receipt_hash": hash_v0(
            "cross_shard_global_conservation_receipt_v0",
            body,
        ),
    }
    if dict(obj) != expected:
        raise ValueError("cross-shard global conservation receipt binding mismatch")
    return expected


def verify_cross_shard_global_conservation_receipt_v0(
    *,
    receipt: Mapping[str, Any],
    posting_summary: Mapping[str, Any],
    effects_artifact: Mapping[str, Any],
    pre_replay_state: CrossShardAppliedEffectsStateV0,
    post_replay_state: CrossShardAppliedEffectsStateV0,
    sharded_settlement_certificate_hash: str | None = None,
) -> CrossShardGlobalConservationReceiptVerdict:
    try:
        expected = build_cross_shard_global_conservation_receipt_v0(
            posting_summary=posting_summary,
            effects_artifact=effects_artifact,
            pre_replay_state=pre_replay_state,
            post_replay_state=post_replay_state,
            sharded_settlement_certificate_hash=sharded_settlement_certificate_hash,
        )
        actual = validate_cross_shard_global_conservation_receipt_v0(receipt)
        if actual != expected:
            raise ValueError("cross-shard global conservation receipt does not match artifacts")
        return CrossShardGlobalConservationReceiptVerdict(
            ok=True,
            error=None,
            receipt=actual,
        )
    except (TypeError, ValueError) as exc:
        return CrossShardGlobalConservationReceiptVerdict(
            ok=False,
            error=str(exc),
        )


def _asset_rows_from_posting_and_effects(
    *,
    posting: Mapping[str, Any],
    artifact: Mapping[str, Any],
) -> list[dict[str, Any]]:
    posting_rows: dict[str, tuple[int, int]] = {}
    for row in posting["postings"]:
        asset_id = _require_id(row.get("asset_id"), name="posting.asset_id")
        debit = _require_non_negative_int(
            row.get("committed_debit_atoms"),
            name="posting.committed_debit_atoms",
        )
        credit = _require_non_negative_int(
            row.get("committed_credit_atoms"),
            name="posting.committed_credit_atoms",
        )
        if debit != credit:
            raise ValueError("cross-shard posting asset row must balance")
        if asset_id in posting_rows:
            raise ValueError("duplicate posting asset row")
        posting_rows[asset_id] = (debit, credit)

    effect_debits: dict[str, int] = defaultdict(int)
    effect_credits: dict[str, int] = defaultdict(int)
    for effect in artifact["effects"]:
        asset_id = _require_id(effect.get("asset_id"), name="effect.asset_id")
        delta = _require_int(effect.get("delta_atoms"), name="effect.delta_atoms")
        if delta < 0:
            effect_debits[asset_id] += -delta
        elif delta > 0:
            effect_credits[asset_id] += delta
        else:
            raise ValueError("effect.delta_atoms must be non-zero")

    if set(posting_rows) != set(effect_debits) or set(posting_rows) != set(effect_credits):
        raise ValueError("posting assets must match effect assets")
    rows: list[dict[str, Any]] = []
    for asset_id in sorted(posting_rows):
        posting_debit, posting_credit = posting_rows[asset_id]
        effect_debit = effect_debits[asset_id]
        effect_credit = effect_credits[asset_id]
        if posting_debit != effect_debit:
            raise ValueError("posting/effects debit mismatch")
        if posting_credit != effect_credit:
            raise ValueError("posting/effects credit mismatch")
        rows.append(
            {
                "asset_id": asset_id,
                "posting_debit_atoms": posting_debit,
                "posting_credit_atoms": posting_credit,
                "effect_debit_atoms": effect_debit,
                "effect_credit_atoms": effect_credit,
            }
        )
    return rows


def _parse_asset_rows(value: object) -> list[dict[str, Any]]:
    if not isinstance(value, list):
        raise TypeError("receipt.asset_rows must be a list")
    rows: list[dict[str, Any]] = []
    seen: set[str] = set()
    for row in value:
        obj = _require_mapping(row, name="receipt.asset_row")
        _reject_unknown_keys(obj, allowed=_ASSET_ROW_KEYS_V0, name="receipt.asset_row")
        asset_id = _require_id(obj.get("asset_id"), name="receipt.asset_row.asset_id")
        if asset_id in seen:
            raise ValueError("duplicate receipt asset row")
        seen.add(asset_id)
        posting_debit = _require_non_negative_int(
            obj.get("posting_debit_atoms"),
            name="receipt.asset_row.posting_debit_atoms",
        )
        posting_credit = _require_non_negative_int(
            obj.get("posting_credit_atoms"),
            name="receipt.asset_row.posting_credit_atoms",
        )
        effect_debit = _require_non_negative_int(
            obj.get("effect_debit_atoms"),
            name="receipt.asset_row.effect_debit_atoms",
        )
        effect_credit = _require_non_negative_int(
            obj.get("effect_credit_atoms"),
            name="receipt.asset_row.effect_credit_atoms",
        )
        if posting_debit != posting_credit:
            raise ValueError("receipt posting asset row must balance")
        if effect_debit != effect_credit:
            raise ValueError("receipt effect asset row must balance")
        if posting_debit != effect_debit or posting_credit != effect_credit:
            raise ValueError("receipt posting/effect asset row mismatch")
        rows.append(
            {
                "asset_id": asset_id,
                "posting_debit_atoms": posting_debit,
                "posting_credit_atoms": posting_credit,
                "effect_debit_atoms": effect_debit,
                "effect_credit_atoms": effect_credit,
            }
        )
    if rows != sorted(rows, key=lambda row: row["asset_id"]):
        raise ValueError("receipt.asset_rows must be sorted by asset_id")
    return rows


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be an object")
    return value


def _reject_unknown_keys(
    value: Mapping[str, Any],
    *,
    allowed: frozenset[str],
    name: str,
) -> None:
    extra = sorted(set(value) - allowed)
    if extra:
        raise ValueError(f"{name} has unsupported fields: {', '.join(extra)}")


def _require_hash(value: object, *, name: str) -> str:
    return canonical_hex_fixed_allow_0x(value, nbytes=ROOT_NBYTES, name=name)


def _require_id(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    if not value:
        raise ValueError(f"{name} must be non-empty")
    if "\x00" in value:
        raise ValueError(f"{name} must not contain NUL")
    return value


def _require_non_negative_int(value: object, *, name: str) -> int:
    out = _require_int(value, name=name)
    if out < 0:
        raise ValueError(f"{name} must be non-negative")
    return out


def _require_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    return int(value)
