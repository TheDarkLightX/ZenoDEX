"""Source-bound application of cross-shard ledger effects to balances."""

from __future__ import annotations

from collections import defaultdict
from collections.abc import Sequence
from dataclasses import dataclass, field
from typing import Any, Mapping

from src.core.cross_shard_decision_certificate import (
    cross_shard_decision_certificate_hash,
)
from src.core.cross_shard_ledger_effects import (
    CROSS_SHARD_LEDGER_EFFECT_SCHEMA_V1,
    CROSS_SHARD_LEDGER_EFFECT_SOURCE_V1,
    CrossShardLedgerEffectV1,
    build_cross_shard_ledger_effects_from_posting_result,
)
from src.core.cross_shard_ledger_posting import (
    build_cross_shard_ledger_posting_summary,
)
from src.core.cross_shard_settlement_admission import (
    verify_cross_shard_settlement_admission_payload,
)
from src.integration.zeno_ledger_tau_export import (
    build_cross_shard_posting_summary_export_v0,
    cross_shard_posting_summary_export_to_build_result_v0,
    validate_cross_shard_posting_summary_export_v0,
)
from src.integration.zeno_ledger_v0 import ROOT_NBYTES, hash_v0
from src.state.balances import BalanceTable
from src.state.canonical import canonical_hex_fixed_allow_0x

CrossShardLedgerEffectsArtifactV0 = dict[str, Any]
CrossShardAppliedEffectsStatePayloadV0 = dict[str, Any]
CrossShardTerminalDecisionEffectAdmissionV0 = dict[str, Any]
CrossShardLedgerNetDeltasV0 = Mapping[tuple[str, str], int]
CROSS_SHARD_LEDGER_EFFECTS_ARTIFACT_SCHEMA_V0 = (
    "zenodex/zeno_ledger/cross_shard_ledger_effects/v0"
)
CROSS_SHARD_APPLIED_EFFECTS_STATE_SCHEMA_V0 = (
    "zenodex/zeno_ledger/cross_shard_applied_effects_state/v0"
)
CROSS_SHARD_TERMINAL_DECISION_EFFECT_ADMISSION_SCHEMA_V0 = (
    "zenodex/zeno_ledger/cross_shard_terminal_decision_effect_admission/v0"
)
CROSS_SHARD_TERMINAL_DECISION_EFFECT_ADMISSION_STATUS_V0 = (
    "verified_terminal_decision_admission"
)

_EFFECTS_ARTIFACT_KEYS_V0 = frozenset(
    {
        "schema",
        "status",
        "source_posting_summary_hash",
        "effect_count",
        "total_debit_atoms",
        "total_credit_atoms",
        "effects",
        "ledger_effects_hash",
    }
)
_EFFECT_ROW_KEYS_V1 = frozenset(
    {
        "schema",
        "asset_id",
        "account_id",
        "delta_atoms",
        "source",
    }
)
_APPLIED_EFFECTS_STATE_KEYS_V0 = frozenset(
    {
        "schema",
        "applied_ledger_effect_hashes",
    }
)
_TERMINAL_ADMISSION_KEYS_V0 = frozenset(
    {
        "schema",
        "status",
        "current_step",
        "sharded_settlement_certificate_hash",
        "posting_summary_hash",
        "ledger_effects_hash",
        "decision_certificate_hashes",
        "committed_transfer_count",
        "rejected_transfer_count",
        "pending_transfer_count",
        "applied_cross_shard_transfer_count",
        "applied_cross_shard_amounts_by_asset",
        "admission_hash",
    }
)
_TERMINAL_ADMISSION_AMOUNT_KEYS_V0 = frozenset(
    {
        "asset_id",
        "amount_atoms",
    }
)


@dataclass(frozen=True)
class CrossShardAppliedEffectsStateV0:
    applied_ledger_effect_hashes: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        if not isinstance(self.applied_ledger_effect_hashes, tuple):
            raise TypeError("applied_ledger_effect_hashes must be a tuple")
        normalized = tuple(
            _require_hash(effect_hash, name="applied_ledger_effect_hashes")
            for effect_hash in self.applied_ledger_effect_hashes
        )
        if tuple(sorted(normalized)) != normalized:
            raise ValueError("applied_ledger_effect_hashes must be sorted")
        if len(set(normalized)) != len(normalized):
            raise ValueError("applied_ledger_effect_hashes must be unique")

    def to_payload(self) -> CrossShardAppliedEffectsStatePayloadV0:
        return {
            "schema": CROSS_SHARD_APPLIED_EFFECTS_STATE_SCHEMA_V0,
            "applied_ledger_effect_hashes": list(self.applied_ledger_effect_hashes),
        }

    def root_hash(self) -> str:
        return hash_v0("cross_shard_applied_effects_state_v0", self.to_payload())

    def contains(self, effect_hash: str) -> bool:
        return _require_hash(effect_hash, name="effect_hash") in self.applied_ledger_effect_hashes

    def add(self, effect_hash: str) -> "CrossShardAppliedEffectsStateV0":
        canonical = _require_hash(effect_hash, name="effect_hash")
        if canonical in self.applied_ledger_effect_hashes:
            return self
        return CrossShardAppliedEffectsStateV0(
            applied_ledger_effect_hashes=tuple(
                sorted((*self.applied_ledger_effect_hashes, canonical))
            )
        )


@dataclass(frozen=True)
class CrossShardLedgerEffectApplicationResult:
    ok: bool
    error: str | None
    applied_ledger_effect_hashes: frozenset[str] = field(default_factory=frozenset)
    applied_effect_count: int | None = None
    total_debit_atoms: int | None = None
    total_credit_atoms: int | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.ok, bool):
            raise TypeError("ok must be bool")
        if self.ok:
            if self.error is not None:
                raise ValueError("accepted cross-shard ledger effect application cannot include error")
            if not isinstance(self.applied_ledger_effect_hashes, frozenset):
                raise TypeError("applied_ledger_effect_hashes must be a frozenset")
            for effect_hash in self.applied_ledger_effect_hashes:
                _require_hash(effect_hash, name="applied_ledger_effect_hashes")
            _require_non_negative_int(
                self.applied_effect_count,
                name="result.applied_effect_count",
            )
            debit = _require_non_negative_int(
                self.total_debit_atoms,
                name="result.total_debit_atoms",
            )
            credit = _require_non_negative_int(
                self.total_credit_atoms,
                name="result.total_credit_atoms",
            )
            if debit != credit:
                raise ValueError("cross-shard ledger effect application totals must balance")
            return
        if not isinstance(self.error, str) or not self.error:
            raise ValueError("rejected cross-shard ledger effect application must include error")
        if (
            self.applied_ledger_effect_hashes
            or self.applied_effect_count is not None
            or self.total_debit_atoms is not None
            or self.total_credit_atoms is not None
        ):
            raise ValueError("rejected cross-shard ledger effect application cannot include artifacts")


@dataclass(frozen=True)
class CrossShardLedgerEffectStateApplicationResult:
    ok: bool
    error: str | None
    pre_replay_state_root: str | None = None
    post_replay_state_root: str | None = None
    post_replay_state: CrossShardAppliedEffectsStateV0 | None = None
    terminal_admission_hash: str | None = None
    applied_effect_count: int | None = None
    total_debit_atoms: int | None = None
    total_credit_atoms: int | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.ok, bool):
            raise TypeError("ok must be bool")
        if self.ok:
            if self.error is not None:
                raise ValueError("accepted cross-shard replay-state application cannot include error")
            _require_hash(self.pre_replay_state_root, name="result.pre_replay_state_root")
            _require_hash(self.post_replay_state_root, name="result.post_replay_state_root")
            if not isinstance(self.post_replay_state, CrossShardAppliedEffectsStateV0):
                raise TypeError("post_replay_state must be CrossShardAppliedEffectsStateV0")
            if self.terminal_admission_hash is not None:
                _require_hash(
                    self.terminal_admission_hash,
                    name="result.terminal_admission_hash",
                )
            _require_non_negative_int(
                self.applied_effect_count,
                name="result.applied_effect_count",
            )
            debit = _require_non_negative_int(
                self.total_debit_atoms,
                name="result.total_debit_atoms",
            )
            credit = _require_non_negative_int(
                self.total_credit_atoms,
                name="result.total_credit_atoms",
            )
            if debit != credit:
                raise ValueError("cross-shard replay-state application totals must balance")
            return
        if not isinstance(self.error, str) or not self.error:
            raise ValueError("rejected cross-shard replay-state application must include error")
        if (
            self.pre_replay_state_root is not None
            or self.post_replay_state_root is not None
            or self.post_replay_state is not None
            or self.terminal_admission_hash is not None
            or self.applied_effect_count is not None
            or self.total_debit_atoms is not None
            or self.total_credit_atoms is not None
        ):
            raise ValueError("rejected cross-shard replay-state application cannot include artifacts")


def empty_cross_shard_applied_effects_state_v0() -> CrossShardAppliedEffectsStateV0:
    return CrossShardAppliedEffectsStateV0()


def cross_shard_applied_effects_state_from_payload_v0(
    payload: Mapping[str, Any],
) -> CrossShardAppliedEffectsStateV0:
    obj = _require_mapping(payload, name="cross_shard_applied_effects_state")
    _reject_unknown_keys(
        obj,
        allowed=_APPLIED_EFFECTS_STATE_KEYS_V0,
        name="cross_shard_applied_effects_state",
    )
    if obj.get("schema") != CROSS_SHARD_APPLIED_EFFECTS_STATE_SCHEMA_V0:
        raise ValueError("cross-shard applied effects state schema mismatch")
    hashes = obj.get("applied_ledger_effect_hashes")
    if not isinstance(hashes, list):
        raise TypeError("applied_ledger_effect_hashes must be a list")
    state = CrossShardAppliedEffectsStateV0(applied_ledger_effect_hashes=tuple(hashes))
    if dict(obj) != state.to_payload():
        raise ValueError("cross-shard applied effects state payload is not canonical")
    return state


def compute_cross_shard_applied_effects_state_root_v0(
    state_or_payload: CrossShardAppliedEffectsStateV0 | Mapping[str, Any],
) -> str:
    state = (
        state_or_payload
        if isinstance(state_or_payload, CrossShardAppliedEffectsStateV0)
        else cross_shard_applied_effects_state_from_payload_v0(state_or_payload)
    )
    return state.root_hash()


def build_cross_shard_ledger_effects_artifact_v0(
    *,
    posting_summary: Mapping[str, Any],
) -> CrossShardLedgerEffectsArtifactV0:
    posting_result = cross_shard_posting_summary_export_to_build_result_v0(
        posting_summary
    )
    effects_result = build_cross_shard_ledger_effects_from_posting_result(
        posting_result
    )
    if not effects_result.ok:
        raise ValueError(f"cross-shard ledger effects rejected: {effects_result.error}")
    effect_payloads = [effect.to_payload() for effect in effects_result.effects]
    artifact_body: CrossShardLedgerEffectsArtifactV0 = {
        "schema": CROSS_SHARD_LEDGER_EFFECTS_ARTIFACT_SCHEMA_V0,
        "status": "derived_from_validated_posting_summary",
        "source_posting_summary_hash": posting_summary["posting_summary_hash"],
        "effect_count": len(effect_payloads),
        "total_debit_atoms": int(effects_result.total_debit_atoms),
        "total_credit_atoms": int(effects_result.total_credit_atoms),
        "effects": effect_payloads,
    }
    return {
        **artifact_body,
        "ledger_effects_hash": hash_v0(
            "cross_shard_ledger_effects_v0",
            artifact_body,
        ),
    }


def validate_cross_shard_ledger_effects_artifact_v0(
    effects_artifact: Mapping[str, Any],
) -> CrossShardLedgerEffectsArtifactV0:
    obj = _require_mapping(effects_artifact, name="cross_shard_ledger_effects")
    _reject_unknown_keys(
        obj,
        allowed=_EFFECTS_ARTIFACT_KEYS_V0,
        name="cross_shard_ledger_effects",
    )
    if obj.get("schema") != CROSS_SHARD_LEDGER_EFFECTS_ARTIFACT_SCHEMA_V0:
        raise ValueError("cross-shard ledger effects schema mismatch")
    if obj.get("status") != "derived_from_validated_posting_summary":
        raise ValueError("cross-shard ledger effects status mismatch")
    source_hash = _require_hash(
        obj.get("source_posting_summary_hash"),
        name="cross_shard_ledger_effects.source_posting_summary_hash",
    )
    effects = _parse_effects(obj.get("effects"))
    effect_count = _require_non_negative_int(
        obj.get("effect_count"),
        name="cross_shard_ledger_effects.effect_count",
    )
    if effect_count != len(effects):
        raise ValueError("cross-shard ledger effects effect_count mismatch")
    total_debit = _require_non_negative_int(
        obj.get("total_debit_atoms"),
        name="cross_shard_ledger_effects.total_debit_atoms",
    )
    total_credit = _require_non_negative_int(
        obj.get("total_credit_atoms"),
        name="cross_shard_ledger_effects.total_credit_atoms",
    )
    if total_debit != _sum_debit_atoms(effects):
        raise ValueError("cross-shard ledger effects debit total mismatch")
    if total_credit != _sum_credit_atoms(effects):
        raise ValueError("cross-shard ledger effects credit total mismatch")
    if total_debit != total_credit:
        raise ValueError("cross-shard ledger effects totals must balance")

    artifact_body: CrossShardLedgerEffectsArtifactV0 = {
        "schema": CROSS_SHARD_LEDGER_EFFECTS_ARTIFACT_SCHEMA_V0,
        "status": "derived_from_validated_posting_summary",
        "source_posting_summary_hash": source_hash,
        "effect_count": effect_count,
        "total_debit_atoms": total_debit,
        "total_credit_atoms": total_credit,
        "effects": [effect.to_payload() for effect in effects],
    }
    expected = {
        **artifact_body,
        "ledger_effects_hash": hash_v0(
            "cross_shard_ledger_effects_v0",
            artifact_body,
        ),
    }
    if dict(obj) != expected:
        raise ValueError("cross-shard ledger effects artifact binding mismatch")
    return expected


def build_cross_shard_terminal_decision_effect_admission_v0(
    *,
    sharded_settlement_payload: Mapping[str, Any],
    decision_certificate_payloads: Sequence[Mapping[str, Any]],
    posting_summary: Mapping[str, Any],
    effects_artifact: Mapping[str, Any],
    current_step: int,
) -> CrossShardTerminalDecisionEffectAdmissionV0:
    """Build the decision-derived admission certificate required before value effects."""

    step = _require_non_negative_int(current_step, name="current_step")
    decision_payloads = _parse_mapping_sequence(
        decision_certificate_payloads,
        name="decision_certificate_payloads",
    )
    admission_result = verify_cross_shard_settlement_admission_payload(
        _require_mapping(sharded_settlement_payload, name="sharded_settlement_payload"),
        decision_certificate_payloads=decision_payloads,
        current_step=step,
    )
    if not admission_result.ok:
        raise ValueError(f"cross-shard terminal admission rejected: {admission_result.error}")
    posting_result = build_cross_shard_ledger_posting_summary(admission_result)
    if not posting_result.ok:
        raise ValueError(f"cross-shard terminal posting rejected: {posting_result.error}")
    expected_posting = build_cross_shard_posting_summary_export_v0(
        posting_result=posting_result
    )
    supplied_posting = validate_cross_shard_posting_summary_export_v0(posting_summary)
    if supplied_posting != expected_posting:
        raise ValueError("terminal decision admission posting summary mismatch")
    artifact = validate_cross_shard_ledger_effects_artifact_v0(effects_artifact)
    if artifact["source_posting_summary_hash"] != supplied_posting["posting_summary_hash"]:
        raise ValueError("terminal decision admission effects source mismatch")

    decision_hashes = tuple(
        sorted(cross_shard_decision_certificate_hash(payload) for payload in decision_payloads)
    )
    body: CrossShardTerminalDecisionEffectAdmissionV0 = {
        "schema": CROSS_SHARD_TERMINAL_DECISION_EFFECT_ADMISSION_SCHEMA_V0,
        "status": CROSS_SHARD_TERMINAL_DECISION_EFFECT_ADMISSION_STATUS_V0,
        "current_step": step,
        "sharded_settlement_certificate_hash": (
            admission_result.sharded_settlement_certificate_hash
        ),
        "posting_summary_hash": supplied_posting["posting_summary_hash"],
        "ledger_effects_hash": artifact["ledger_effects_hash"],
        "decision_certificate_hashes": list(decision_hashes),
        "committed_transfer_count": admission_result.committed_transfer_count,
        "rejected_transfer_count": admission_result.rejected_transfer_count,
        "pending_transfer_count": admission_result.pending_transfer_count,
        "applied_cross_shard_transfer_count": (
            admission_result.applied_cross_shard_transfer_count
        ),
        "applied_cross_shard_amounts_by_asset": [
            {"asset_id": asset_id, "amount_atoms": amount_atoms}
            for asset_id, amount_atoms in admission_result.applied_cross_shard_amounts_by_asset
        ],
    }
    return {
        **body,
        "admission_hash": hash_v0(
            "cross_shard_terminal_decision_effect_admission_v0",
            body,
        ),
    }


def validate_cross_shard_terminal_decision_effect_admission_v0(
    terminal_admission: Mapping[str, Any],
    *,
    posting_summary: Mapping[str, Any],
    effects_artifact: Mapping[str, Any],
) -> CrossShardTerminalDecisionEffectAdmissionV0:
    obj = _require_mapping(
        terminal_admission,
        name="cross_shard_terminal_decision_effect_admission",
    )
    _reject_unknown_keys(
        obj,
        allowed=_TERMINAL_ADMISSION_KEYS_V0,
        name="cross_shard_terminal_decision_effect_admission",
    )
    if obj.get("schema") != CROSS_SHARD_TERMINAL_DECISION_EFFECT_ADMISSION_SCHEMA_V0:
        raise ValueError("cross-shard terminal decision effect admission schema mismatch")
    if obj.get("status") != CROSS_SHARD_TERMINAL_DECISION_EFFECT_ADMISSION_STATUS_V0:
        raise ValueError("cross-shard terminal decision effect admission status mismatch")
    step = _require_non_negative_int(
        obj.get("current_step"),
        name="cross_shard_terminal_decision_effect_admission.current_step",
    )
    settlement_hash = _require_hash(
        obj.get("sharded_settlement_certificate_hash"),
        name="cross_shard_terminal_decision_effect_admission.sharded_settlement_certificate_hash",
    )
    posting_hash = _require_hash(
        obj.get("posting_summary_hash"),
        name="cross_shard_terminal_decision_effect_admission.posting_summary_hash",
    )
    ledger_effects_hash = _require_hash(
        obj.get("ledger_effects_hash"),
        name="cross_shard_terminal_decision_effect_admission.ledger_effects_hash",
    )
    decision_hashes = _parse_hash_list(
        obj.get("decision_certificate_hashes"),
        name="cross_shard_terminal_decision_effect_admission.decision_certificate_hashes",
    )
    committed_count = _require_non_negative_int(
        obj.get("committed_transfer_count"),
        name="cross_shard_terminal_decision_effect_admission.committed_transfer_count",
    )
    rejected_count = _require_non_negative_int(
        obj.get("rejected_transfer_count"),
        name="cross_shard_terminal_decision_effect_admission.rejected_transfer_count",
    )
    pending_count = _require_non_negative_int(
        obj.get("pending_transfer_count"),
        name="cross_shard_terminal_decision_effect_admission.pending_transfer_count",
    )
    applied_count = _require_non_negative_int(
        obj.get("applied_cross_shard_transfer_count"),
        name="cross_shard_terminal_decision_effect_admission.applied_cross_shard_transfer_count",
    )
    if applied_count != committed_count:
        raise ValueError("terminal decision admission applied count must equal commit count")
    amounts = _parse_terminal_admission_amount_rows(
        obj.get("applied_cross_shard_amounts_by_asset")
    )
    supplied_posting = validate_cross_shard_posting_summary_export_v0(posting_summary)
    artifact = validate_cross_shard_ledger_effects_artifact_v0(effects_artifact)
    if supplied_posting["sharded_settlement_certificate_hash"] != settlement_hash:
        raise ValueError("terminal decision admission settlement hash mismatch")
    if supplied_posting["posting_summary_hash"] != posting_hash:
        raise ValueError("terminal decision admission posting summary hash mismatch")
    if artifact["source_posting_summary_hash"] != posting_hash:
        raise ValueError("terminal decision admission effects source mismatch")
    if artifact["ledger_effects_hash"] != ledger_effects_hash:
        raise ValueError("terminal decision admission ledger effects hash mismatch")

    body: CrossShardTerminalDecisionEffectAdmissionV0 = {
        "schema": CROSS_SHARD_TERMINAL_DECISION_EFFECT_ADMISSION_SCHEMA_V0,
        "status": CROSS_SHARD_TERMINAL_DECISION_EFFECT_ADMISSION_STATUS_V0,
        "current_step": step,
        "sharded_settlement_certificate_hash": settlement_hash,
        "posting_summary_hash": posting_hash,
        "ledger_effects_hash": ledger_effects_hash,
        "decision_certificate_hashes": list(decision_hashes),
        "committed_transfer_count": committed_count,
        "rejected_transfer_count": rejected_count,
        "pending_transfer_count": pending_count,
        "applied_cross_shard_transfer_count": applied_count,
        "applied_cross_shard_amounts_by_asset": [
            {"asset_id": asset_id, "amount_atoms": amount_atoms}
            for asset_id, amount_atoms in amounts
        ],
    }
    expected = {
        **body,
        "admission_hash": hash_v0(
            "cross_shard_terminal_decision_effect_admission_v0",
            body,
        ),
    }
    if dict(obj) != expected:
        raise ValueError("cross-shard terminal decision effect admission binding mismatch")
    return expected


def verify_cross_shard_terminal_decision_effect_admission_source_v0(
    terminal_admission: Mapping[str, Any],
    *,
    posting_summary: Mapping[str, Any],
    effects_artifact: Mapping[str, Any],
    sharded_settlement_payload: Mapping[str, Any],
    decision_certificate_payloads: Sequence[Mapping[str, Any]],
) -> CrossShardTerminalDecisionEffectAdmissionV0:
    supplied = validate_cross_shard_terminal_decision_effect_admission_v0(
        terminal_admission,
        posting_summary=posting_summary,
        effects_artifact=effects_artifact,
    )
    rebuilt = build_cross_shard_terminal_decision_effect_admission_v0(
        sharded_settlement_payload=sharded_settlement_payload,
        decision_certificate_payloads=decision_certificate_payloads,
        posting_summary=posting_summary,
        effects_artifact=effects_artifact,
        current_step=supplied["current_step"],
    )
    if supplied != rebuilt:
        raise ValueError("terminal decision admission source verification mismatch")
    return supplied


def apply_terminal_cross_shard_ledger_effects_to_state_v0(
    *,
    balances: BalanceTable,
    effects_artifact: Mapping[str, Any],
    body_pinned_posting_summary_hash: str,
    replay_state: CrossShardAppliedEffectsStateV0,
    terminal_admission: Mapping[str, Any],
    posting_summary: Mapping[str, Any],
    sharded_settlement_payload: Mapping[str, Any] | None = None,
    decision_certificate_payloads: Sequence[Mapping[str, Any]] | None = None,
) -> CrossShardLedgerEffectStateApplicationResult:
    try:
        if sharded_settlement_payload is None or decision_certificate_payloads is None:
            raise ValueError(
                "terminal decision source payloads required before applying cross-shard ledger effects"
            )
        admission = verify_cross_shard_terminal_decision_effect_admission_source_v0(
            terminal_admission,
            posting_summary=posting_summary,
            effects_artifact=effects_artifact,
            sharded_settlement_payload=sharded_settlement_payload,
            decision_certificate_payloads=decision_certificate_payloads,
        )
        result = apply_cross_shard_ledger_effects_to_state_v0(
            balances=balances,
            effects_artifact=effects_artifact,
            body_pinned_posting_summary_hash=body_pinned_posting_summary_hash,
            replay_state=replay_state,
        )
        if not result.ok:
            return result
        return CrossShardLedgerEffectStateApplicationResult(
            ok=True,
            error=None,
            pre_replay_state_root=result.pre_replay_state_root,
            post_replay_state_root=result.post_replay_state_root,
            post_replay_state=result.post_replay_state,
            terminal_admission_hash=str(admission["admission_hash"]),
            applied_effect_count=result.applied_effect_count,
            total_debit_atoms=result.total_debit_atoms,
            total_credit_atoms=result.total_credit_atoms,
        )
    except (TypeError, ValueError) as exc:
        return CrossShardLedgerEffectStateApplicationResult(ok=False, error=str(exc))


def apply_terminal_cross_shard_ledger_effects_to_balances_v0(
    *,
    balances: BalanceTable,
    effects_artifact: Mapping[str, Any],
    body_pinned_posting_summary_hash: str,
    applied_ledger_effect_hashes: frozenset[str],
    terminal_admission: Mapping[str, Any],
    posting_summary: Mapping[str, Any],
    sharded_settlement_payload: Mapping[str, Any] | None = None,
    decision_certificate_payloads: Sequence[Mapping[str, Any]] | None = None,
) -> CrossShardLedgerEffectApplicationResult:
    try:
        replay_state = CrossShardAppliedEffectsStateV0(
            applied_ledger_effect_hashes=tuple(
                sorted(_require_hash_set(applied_ledger_effect_hashes))
            )
        )
        result = apply_terminal_cross_shard_ledger_effects_to_state_v0(
            balances=balances,
            effects_artifact=effects_artifact,
            body_pinned_posting_summary_hash=body_pinned_posting_summary_hash,
            replay_state=replay_state,
            terminal_admission=terminal_admission,
            posting_summary=posting_summary,
            sharded_settlement_payload=sharded_settlement_payload,
            decision_certificate_payloads=decision_certificate_payloads,
        )
        if not result.ok:
            raise ValueError(str(result.error))
        return CrossShardLedgerEffectApplicationResult(
            ok=True,
            error=None,
            applied_ledger_effect_hashes=frozenset(
                result.post_replay_state.applied_ledger_effect_hashes  # type: ignore[union-attr]
            ),
            applied_effect_count=result.applied_effect_count,
            total_debit_atoms=result.total_debit_atoms,
            total_credit_atoms=result.total_credit_atoms,
        )
    except (TypeError, ValueError) as exc:
        return CrossShardLedgerEffectApplicationResult(ok=False, error=str(exc))


def apply_cross_shard_ledger_effects_to_balances_v0(
    *,
    balances: BalanceTable,
    effects_artifact: Mapping[str, Any],
    body_pinned_posting_summary_hash: str,
    applied_ledger_effect_hashes: frozenset[str],
) -> CrossShardLedgerEffectApplicationResult:
    try:
        applied_hashes = _require_hash_set(applied_ledger_effect_hashes)
        replay_state = CrossShardAppliedEffectsStateV0(
            applied_ledger_effect_hashes=tuple(sorted(applied_hashes))
        )
        state_result = apply_cross_shard_ledger_effects_to_state_v0(
            balances=balances,
            effects_artifact=effects_artifact,
            body_pinned_posting_summary_hash=body_pinned_posting_summary_hash,
            replay_state=replay_state,
        )
        if not state_result.ok:
            raise ValueError(str(state_result.error))
        return CrossShardLedgerEffectApplicationResult(
            ok=True,
            error=None,
            applied_ledger_effect_hashes=frozenset(
                state_result.post_replay_state.applied_ledger_effect_hashes  # type: ignore[union-attr]
            ),
            applied_effect_count=state_result.applied_effect_count,
            total_debit_atoms=state_result.total_debit_atoms,
            total_credit_atoms=state_result.total_credit_atoms,
        )
    except (TypeError, ValueError) as exc:
        return CrossShardLedgerEffectApplicationResult(ok=False, error=str(exc))


def apply_cross_shard_ledger_effects_to_state_v0(
    *,
    balances: BalanceTable,
    effects_artifact: Mapping[str, Any],
    body_pinned_posting_summary_hash: str,
    replay_state: CrossShardAppliedEffectsStateV0,
) -> CrossShardLedgerEffectStateApplicationResult:
    try:
        if not isinstance(balances, BalanceTable):
            raise TypeError("balances must be BalanceTable")
        if not isinstance(replay_state, CrossShardAppliedEffectsStateV0):
            raise TypeError("replay_state must be CrossShardAppliedEffectsStateV0")
        pre_root = replay_state.root_hash()
        pinned_hash = _require_hash(
            body_pinned_posting_summary_hash,
            name="body_pinned_posting_summary_hash",
        )
        artifact = validate_cross_shard_ledger_effects_artifact_v0(effects_artifact)
        if artifact["source_posting_summary_hash"] != pinned_hash:
            raise ValueError("cross-shard ledger effects source hash is not body-pinned")
        ledger_effects_hash = str(artifact["ledger_effects_hash"])
        if replay_state.contains(ledger_effects_hash):
            raise ValueError("cross-shard ledger effects artifact already applied")
        effects = _parse_effects(artifact["effects"])
        net_deltas = _aggregate_net_deltas(effects)
        _precheck_balances(balances=balances, net_deltas=net_deltas)
        post_replay_state = replay_state.add(ledger_effects_hash)
        for account_id, asset_id in sorted(net_deltas):
            balances.add(account_id, asset_id, net_deltas[(account_id, asset_id)])
        return CrossShardLedgerEffectStateApplicationResult(
            ok=True,
            error=None,
            pre_replay_state_root=pre_root,
            post_replay_state_root=post_replay_state.root_hash(),
            post_replay_state=post_replay_state,
            applied_effect_count=len(effects),
            total_debit_atoms=int(artifact["total_debit_atoms"]),
            total_credit_atoms=int(artifact["total_credit_atoms"]),
        )
    except (TypeError, ValueError) as exc:
        return CrossShardLedgerEffectStateApplicationResult(ok=False, error=str(exc))


def _aggregate_net_deltas(
    effects: tuple[CrossShardLedgerEffectV1, ...],
) -> CrossShardLedgerNetDeltasV0:
    net: dict[tuple[str, str], int] = defaultdict(int)
    for effect in effects:
        net[(effect.account_id, effect.asset_id)] += effect.delta_atoms
    return dict(net)


def _precheck_balances(
    *,
    balances: BalanceTable,
    net_deltas: Mapping[tuple[str, str], int],
) -> None:
    for account_id, asset_id in sorted(net_deltas):
        if balances.get(account_id, asset_id) + net_deltas[(account_id, asset_id)] < 0:
            raise ValueError("cross-shard ledger effects would make balance negative")


def _parse_effects(value: object) -> tuple[CrossShardLedgerEffectV1, ...]:
    if not isinstance(value, list):
        raise TypeError("cross_shard_ledger_effects.effects must be a list")
    return tuple(_parse_effect(row, index=index) for index, row in enumerate(value))


def _parse_effect(value: object, *, index: int) -> CrossShardLedgerEffectV1:
    obj = _require_mapping(value, name=f"cross_shard_ledger_effects.effects[{index}]")
    _reject_unknown_keys(
        obj,
        allowed=_EFFECT_ROW_KEYS_V1,
        name=f"cross_shard_ledger_effects.effects[{index}]",
    )
    if obj.get("schema") != CROSS_SHARD_LEDGER_EFFECT_SCHEMA_V1:
        raise ValueError("cross-shard ledger effect schema mismatch")
    if obj.get("source") != CROSS_SHARD_LEDGER_EFFECT_SOURCE_V1:
        raise ValueError("cross-shard ledger effect source mismatch")
    return CrossShardLedgerEffectV1(
        asset_id=_require_id(
            obj.get("asset_id"),
            name=f"cross_shard_ledger_effects.effects[{index}].asset_id",
        ),
        account_id=_require_id(
            obj.get("account_id"),
            name=f"cross_shard_ledger_effects.effects[{index}].account_id",
        ),
        delta_atoms=_require_int(
            obj.get("delta_atoms"),
            name=f"cross_shard_ledger_effects.effects[{index}].delta_atoms",
        ),
        source=_require_id(
            obj.get("source"),
            name=f"cross_shard_ledger_effects.effects[{index}].source",
        ),
    )


def _sum_debit_atoms(effects: tuple[CrossShardLedgerEffectV1, ...]) -> int:
    return sum(-effect.delta_atoms for effect in effects if effect.delta_atoms < 0)


def _sum_credit_atoms(effects: tuple[CrossShardLedgerEffectV1, ...]) -> int:
    return sum(effect.delta_atoms for effect in effects if effect.delta_atoms > 0)


def _require_hash_set(value: object) -> frozenset[str]:
    if not isinstance(value, frozenset):
        raise TypeError("applied_ledger_effect_hashes must be a frozenset")
    return frozenset(
        _require_hash(effect_hash, name="applied_ledger_effect_hashes")
        for effect_hash in value
    )


def _parse_hash_list(value: object, *, name: str) -> tuple[str, ...]:
    if not isinstance(value, list):
        raise TypeError(f"{name} must be a list")
    hashes = tuple(
        _require_hash(item, name=f"{name}[{index}]")
        for index, item in enumerate(value)
    )
    if tuple(sorted(hashes)) != hashes:
        raise ValueError(f"{name} must be sorted")
    if len(set(hashes)) != len(hashes):
        raise ValueError(f"{name} must be unique")
    return hashes


def _parse_mapping_sequence(
    value: Sequence[Mapping[str, Any]],
    *,
    name: str,
) -> tuple[Mapping[str, Any], ...]:
    if not isinstance(value, Sequence) or isinstance(value, (str, bytes, bytearray)):
        raise TypeError(f"{name} must be a sequence")
    return tuple(_require_mapping(item, name=f"{name}[{index}]") for index, item in enumerate(value))


def _parse_terminal_admission_amount_rows(value: object) -> tuple[tuple[str, int], ...]:
    if not isinstance(value, list):
        raise TypeError("terminal admission amount rows must be a list")
    rows: list[tuple[str, int]] = []
    previous_asset: str | None = None
    for index, item in enumerate(value):
        row = _require_mapping(item, name=f"terminal_admission.amounts[{index}]")
        _reject_unknown_keys(
            row,
            allowed=_TERMINAL_ADMISSION_AMOUNT_KEYS_V0,
            name=f"terminal_admission.amounts[{index}]",
        )
        asset_id = _require_id(
            row.get("asset_id"),
            name=f"terminal_admission.amounts[{index}].asset_id",
        )
        amount_atoms = _require_non_negative_int(
            row.get("amount_atoms"),
            name=f"terminal_admission.amounts[{index}].amount_atoms",
        )
        if amount_atoms == 0:
            raise ValueError("terminal admission amount row must be positive")
        if previous_asset is not None and asset_id <= previous_asset:
            raise ValueError("terminal admission amount rows must be strictly sorted")
        previous_asset = asset_id
        rows.append((asset_id, amount_atoms))
    return tuple(rows)


def _reject_unknown_keys(
    value: Mapping[str, Any],
    *,
    allowed: frozenset[str],
    name: str,
) -> None:
    extra = sorted(set(value.keys()) - set(allowed))
    if extra:
        raise ValueError(f"{name} contains unknown keys: {extra}")


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a JSON object")
    return value


def _require_id(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    if not value:
        raise ValueError(f"{name} must be non-empty")
    if "\x00" in value:
        raise ValueError(f"{name} must not contain NUL")
    return value


def _require_hash(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    canonical = canonical_hex_fixed_allow_0x(
        value,
        nbytes=ROOT_NBYTES,
        name=name,
    )
    if value != canonical:
        raise ValueError(f"{name} must be canonical lowercase 0x-prefixed hex")
    return canonical


def _require_non_negative_int(value: object, *, name: str) -> int:
    out = _require_int(value, name=name)
    if out < 0:
        raise ValueError(f"{name} must be non-negative")
    return out


def _require_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    return int(value)
