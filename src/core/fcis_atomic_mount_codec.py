"""Canonical codecs and same-candidate builders for the FCIS M5 authority graph."""

from __future__ import annotations

from ..state.canonical import domain_sep_bytes, encode_bytes, encode_uvarint, sha256_hex
from ..state.committed_dex_snapshot import canonical_snapshot_bytes_from_committed_state_v1
from .fcis_atomic_mount_values import (
    FCIS_M5_ALGORITHM_ID_V1,
    FCIS_M5_ALGORITHM_VERSION_V1,
    FCIS_M5_CODEC_VERSION_V1,
    FCIS_M5_SCHEMA_VERSION_V1,
    MAX_AUTHORITY_PAYLOAD_BYTES_V1,
    MAX_OUTBOX_RECORDS_V1,
    FCISAcceptV1,
    FCISAuthorityPayloadDomainV1,
    FCISCommitBundleV1,
    FCISCommitPlanV1,
    FCISCommittedDexStateV1,
    FCISCommittedFailureV1,
    FCISDecisionV1,
    FCISOutboxEffectV1,
    FCISOutboxPlanV1,
    FCISOutboxRecordV1,
    FCISReceiptOutcomeV1,
    FCISReceiptV1,
    FCISRejectV1,
    FCISReplayUpdateV1,
    FCISRootBoundPayloadV1,
    require_digest_v1,
    require_replay_updates_v1,
    require_text_v1,
)

MAX_OUTBOX_TOTAL_PAYLOAD_BYTES_V1 = 16_000_000


def _digest_bytes_v1(value: str) -> bytes:
    return bytes.fromhex(require_digest_v1(value, "digest")[2:])


def _encode_text_v1(value: str) -> bytes:
    return encode_bytes(require_text_v1(value, "text", allow_empty=True).encode("utf-8"))


def root_bound_payload_digest_v1(
    domain: FCISAuthorityPayloadDomainV1,
    canonical_bytes: bytes,
) -> str:
    if type(domain) is not FCISAuthorityPayloadDomainV1:
        raise TypeError("authority payload domain must be exact")
    if type(canonical_bytes) is not bytes:
        raise TypeError("authority payload bytes must be exact bytes")
    if len(canonical_bytes) > MAX_AUTHORITY_PAYLOAD_BYTES_V1:
        raise ValueError("authority payload exceeds its byte budget")
    return sha256_hex(
        domain_sep_bytes(domain.value, version=FCIS_M5_CODEC_VERSION_V1) + canonical_bytes
    )


def _validate_root_bound_payload_v1(
    payload: FCISRootBoundPayloadV1,
    *,
    expected_domain: FCISAuthorityPayloadDomainV1 | None = None,
) -> None:
    if type(payload) is not FCISRootBoundPayloadV1:
        raise TypeError("authority payload must be exact")
    if type(payload.domain) is not FCISAuthorityPayloadDomainV1:
        raise TypeError("authority payload domain must be exact")
    if expected_domain is not None and payload.domain is not expected_domain:
        raise ValueError("authority payload uses the wrong domain")
    if type(payload.canonical_bytes) is not bytes:
        raise TypeError("authority payload bytes must be exact bytes")
    require_digest_v1(payload.root, "authority payload root")
    expected_root = root_bound_payload_digest_v1(payload.domain, payload.canonical_bytes)
    if payload.root != expected_root:
        raise ValueError("authority payload root does not bind its canonical bytes")


def bind_authority_payload_v1(
    domain: FCISAuthorityPayloadDomainV1,
    canonical_bytes: bytes,
) -> FCISRootBoundPayloadV1:
    if type(domain) is not FCISAuthorityPayloadDomainV1:
        raise TypeError("authority payload domain must be exact")
    if type(canonical_bytes) is not bytes:
        raise TypeError("authority payload bytes must be exact bytes")
    owned = bytes(canonical_bytes)
    return FCISRootBoundPayloadV1(
        domain=domain,
        canonical_bytes=owned,
        root=root_bound_payload_digest_v1(domain, owned),
    )


def _encode_root_bound_payload_v1(payload: FCISRootBoundPayloadV1) -> bytes:
    _validate_root_bound_payload_v1(payload)
    return (
        encode_uvarint(list(FCISAuthorityPayloadDomainV1).index(payload.domain) + 1)
        + encode_bytes(payload.canonical_bytes)
        + _digest_bytes_v1(payload.root)
    )


def canonical_committed_state_bytes_v1(state: FCISCommittedDexStateV1) -> bytes:
    if type(state) is not FCISCommittedDexStateV1:
        raise TypeError("committed DEX state must be exact")
    if type(state.snapshot_version) is not int or state.snapshot_version <= 0:
        raise TypeError("snapshot_version must be an exact positive int")
    return canonical_snapshot_bytes_from_committed_state_v1(
        version=state.snapshot_version,
        balances=state.balances,
        pools=state.pools,
        lp_balances=state.lp_balances,
        nonces=state.nonces,
        fee_accumulator=state.fee_accumulator,
        vault=state.vault,
        oracle=state.oracle,
        perps=state.perps,
    )


def committed_state_root_v1(state: FCISCommittedDexStateV1) -> str:
    canonical = canonical_committed_state_bytes_v1(state)
    return sha256_hex(domain_sep_bytes("dex_snapshot", version=state.snapshot_version) + canonical)


def _encode_replay_updates_v1(updates: tuple[FCISReplayUpdateV1, ...]) -> bytes:
    exact = require_replay_updates_v1(updates)
    out = bytearray(encode_uvarint(len(exact)))
    for update in exact:
        out += bytes.fromhex(update.pubkey[2:])
        out += encode_uvarint(update.expected_last)
        out += encode_uvarint(update.new_last)
    return bytes(out)


def _encode_receipt_body_v1(
    *,
    outcome: FCISReceiptOutcomeV1,
    code: str,
    public_reason: str,
    detail: FCISRootBoundPayloadV1 | None,
) -> bytes:
    if type(outcome) is not FCISReceiptOutcomeV1:
        raise TypeError("receipt outcome must be exact")
    exact_code = require_text_v1(code, "receipt code")
    exact_reason = require_text_v1(public_reason, "receipt public_reason")
    out = bytearray(domain_sep_bytes("fcis_m5_receipt_body", version=FCIS_M5_CODEC_VERSION_V1))
    out += encode_uvarint(list(FCISReceiptOutcomeV1).index(outcome) + 1)
    out += _encode_text_v1(exact_code)
    out += _encode_text_v1(exact_reason)
    out += encode_uvarint(0 if detail is None else 1)
    if detail is not None:
        _validate_root_bound_payload_v1(
            detail,
            expected_domain=FCISAuthorityPayloadDomainV1.RECEIPT_DETAIL,
        )
        out += _encode_root_bound_payload_v1(detail)
    return bytes(out)


def _validate_receipt_v1(receipt: FCISReceiptV1) -> None:
    if type(receipt) is not FCISReceiptV1:
        raise TypeError("receipt must be exact")
    _encode_receipt_body_v1(
        outcome=receipt.outcome,
        code=receipt.code,
        public_reason=receipt.public_reason,
        detail=receipt.detail,
    )
    if receipt.outcome is FCISReceiptOutcomeV1.REJECT:
        if receipt.candidate_root is not None:
            raise ValueError("ordinary rejection receipt cannot bind a candidate")
    else:
        require_digest_v1(receipt.candidate_root, "receipt candidate root")


def encode_receipt_v1(receipt: FCISReceiptV1) -> bytes:
    _validate_receipt_v1(receipt)
    out = bytearray(domain_sep_bytes("fcis_m5_receipt", version=FCIS_M5_CODEC_VERSION_V1))
    out += encode_uvarint(0 if receipt.candidate_root is None else 1)
    if receipt.candidate_root is not None:
        out += _digest_bytes_v1(receipt.candidate_root)
    out += encode_bytes(
        _encode_receipt_body_v1(
            outcome=receipt.outcome,
            code=receipt.code,
            public_reason=receipt.public_reason,
            detail=receipt.detail,
        )
    )
    return bytes(out)


def receipt_root_v1(receipt: FCISReceiptV1) -> str:
    return sha256_hex(encode_receipt_v1(receipt))


def outbox_idempotency_key_v1(
    receipt_root: str,
    effect_index: int,
    effect_identity: str,
) -> str:
    require_digest_v1(receipt_root, "outbox receipt root")
    if type(effect_index) is not int or effect_index < 0:
        raise TypeError("outbox effect index must be an exact nonnegative int")
    require_text_v1(effect_identity, "outbox effect identity")
    return sha256_hex(
        domain_sep_bytes("fcis_m5_outbox_id", version=FCIS_M5_CODEC_VERSION_V1)
        + _digest_bytes_v1(receipt_root)
        + encode_uvarint(effect_index)
        + _encode_text_v1(effect_identity)
    )


def _validate_outbox_effects_v1(
    effects: tuple[FCISOutboxEffectV1, ...],
) -> tuple[FCISOutboxEffectV1, ...]:
    if type(effects) is not tuple:
        raise TypeError("outbox effects must be an exact tuple")
    if len(effects) > MAX_OUTBOX_RECORDS_V1:
        raise ValueError("outbox effects exceed their item budget")
    total_payload_bytes = 0
    for effect in effects:
        if type(effect) is not FCISOutboxEffectV1:
            raise TypeError("outbox effect must be exact")
        require_text_v1(effect.effect_identity, "outbox effect identity")
        if type(effect.canonical_payload) is not bytes:
            raise TypeError("outbox effect payload must be exact bytes")
        if len(effect.canonical_payload) > MAX_AUTHORITY_PAYLOAD_BYTES_V1:
            raise ValueError("outbox effect payload exceeds its byte budget")
        total_payload_bytes += len(effect.canonical_payload)
        if total_payload_bytes > MAX_OUTBOX_TOTAL_PAYLOAD_BYTES_V1:
            raise ValueError("outbox effects exceed their aggregate byte budget")
    return effects


def _encode_outbox_effect_material_v1(
    effects: tuple[FCISOutboxEffectV1, ...],
) -> bytes:
    exact = _validate_outbox_effects_v1(effects)
    out = bytearray(encode_uvarint(len(exact)))
    for effect in exact:
        out += _encode_text_v1(effect.effect_identity)
        out += encode_bytes(effect.canonical_payload)
    return bytes(out)


def _validate_outbox_plan_v1(
    plan: FCISOutboxPlanV1,
    *,
    expected_candidate_root: str | None = None,
    expected_receipt_root: str | None = None,
) -> None:
    if type(plan) is not FCISOutboxPlanV1:
        raise TypeError("outbox plan must be exact")
    require_digest_v1(plan.candidate_root, "outbox-plan candidate root")
    require_digest_v1(plan.receipt_root, "outbox-plan receipt root")
    if expected_candidate_root is not None and plan.candidate_root != expected_candidate_root:
        raise ValueError("outbox plan belongs to a different candidate")
    if expected_receipt_root is not None and plan.receipt_root != expected_receipt_root:
        raise ValueError("outbox plan is not bound to its receipt")
    if type(plan.records) is not tuple:
        raise TypeError("outbox records must be an exact tuple")
    if len(plan.records) > MAX_OUTBOX_RECORDS_V1:
        raise ValueError("outbox records exceed their item budget")
    total_payload_bytes = 0
    for index, record in enumerate(plan.records):
        if type(record) is not FCISOutboxRecordV1:
            raise TypeError("outbox record must be exact")
        require_digest_v1(record.candidate_root, "outbox candidate root")
        require_digest_v1(record.receipt_root, "outbox receipt root")
        if type(record.effect_index) is not int or record.effect_index != index:
            raise ValueError("outbox indices must be contiguous protocol order")
        require_text_v1(record.effect_identity, "outbox effect identity")
        _validate_root_bound_payload_v1(
            record.payload,
            expected_domain=FCISAuthorityPayloadDomainV1.OUTBOX_PAYLOAD,
        )
        total_payload_bytes += len(record.payload.canonical_bytes)
        if total_payload_bytes > MAX_OUTBOX_TOTAL_PAYLOAD_BYTES_V1:
            raise ValueError("outbox records exceed their aggregate byte budget")
        if record.candidate_root != plan.candidate_root:
            raise ValueError("outbox record candidate root mismatch")
        if record.receipt_root != plan.receipt_root:
            raise ValueError("outbox record receipt root mismatch")
        require_digest_v1(record.idempotency_key, "outbox idempotency key")
        expected_key = outbox_idempotency_key_v1(
            record.receipt_root,
            record.effect_index,
            record.effect_identity,
        )
        if record.idempotency_key != expected_key:
            raise ValueError("outbox idempotency key is not receipt-derived")


def _encode_outbox_record_material_v1(plan: FCISOutboxPlanV1) -> bytes:
    _validate_outbox_plan_v1(plan)
    out = bytearray(encode_uvarint(len(plan.records)))
    for record in plan.records:
        out += _encode_text_v1(record.effect_identity)
        out += encode_bytes(record.payload.canonical_bytes)
    return bytes(out)


def build_outbox_plan_v1(
    *,
    candidate_root: str,
    receipt_root: str,
    effects: tuple[FCISOutboxEffectV1, ...],
) -> FCISOutboxPlanV1:
    require_digest_v1(candidate_root, "outbox-plan candidate root")
    require_digest_v1(receipt_root, "outbox-plan receipt root")
    exact_effects = _validate_outbox_effects_v1(effects)
    records: list[FCISOutboxRecordV1] = []
    for index, effect in enumerate(exact_effects):
        payload = bind_authority_payload_v1(
            FCISAuthorityPayloadDomainV1.OUTBOX_PAYLOAD,
            effect.canonical_payload,
        )
        records.append(
            FCISOutboxRecordV1(
                candidate_root=candidate_root,
                receipt_root=receipt_root,
                effect_index=index,
                effect_identity=effect.effect_identity,
                payload=payload,
                idempotency_key=outbox_idempotency_key_v1(
                    receipt_root,
                    index,
                    effect.effect_identity,
                ),
            )
        )
    return FCISOutboxPlanV1(candidate_root, receipt_root, tuple(records))


def _encode_outbox_plan_v1(plan: FCISOutboxPlanV1) -> bytes:
    _validate_outbox_plan_v1(plan)
    out = bytearray(_digest_bytes_v1(plan.candidate_root))
    out += _digest_bytes_v1(plan.receipt_root)
    out += encode_uvarint(len(plan.records))
    for record in plan.records:
        out += encode_uvarint(record.effect_index)
        out += _encode_text_v1(record.effect_identity)
        out += _encode_root_bound_payload_v1(record.payload)
        out += _digest_bytes_v1(record.idempotency_key)
    return bytes(out)


def _validate_commit_plan_v1(plan: FCISCommitPlanV1) -> None:
    if type(plan) is not FCISCommitPlanV1:
        raise TypeError("commit plan must be exact")
    require_digest_v1(plan.candidate_root, "commit-plan candidate root")
    _validate_root_bound_payload_v1(
        plan.canonical_patch,
        expected_domain=FCISAuthorityPayloadDomainV1.CANONICAL_PATCH,
    )
    _validate_root_bound_payload_v1(
        plan.value_plan,
        expected_domain=FCISAuthorityPayloadDomainV1.VALUE_PLAN,
    )
    require_replay_updates_v1(plan.replay_updates)
    _validate_outbox_plan_v1(
        plan.outbox_plan,
        expected_candidate_root=plan.candidate_root,
    )


def encode_commit_plan_v1(plan: FCISCommitPlanV1) -> bytes:
    _validate_commit_plan_v1(plan)
    return (
        domain_sep_bytes("fcis_m5_commit_plan", version=FCIS_M5_CODEC_VERSION_V1)
        + _digest_bytes_v1(plan.candidate_root)
        + _encode_root_bound_payload_v1(plan.canonical_patch)
        + _encode_root_bound_payload_v1(plan.value_plan)
        + _encode_replay_updates_v1(plan.replay_updates)
        + _encode_outbox_plan_v1(plan.outbox_plan)
    )


def commit_plan_root_v1(plan: FCISCommitPlanV1) -> str:
    return sha256_hex(encode_commit_plan_v1(plan))


def _derive_candidate_root_from_material_v1(
    *,
    expected_pre_root: str,
    execution_context_hash: str,
    command_or_batch_root: str,
    next_state_root: str,
    canonical_patch: FCISRootBoundPayloadV1,
    value_plan: FCISRootBoundPayloadV1,
    replay_updates: tuple[FCISReplayUpdateV1, ...],
    outbox_material: bytes,
    receipt_body: bytes,
) -> str:
    if type(outbox_material) is not bytes or type(receipt_body) is not bytes:
        raise TypeError("candidate material must be exact bytes")
    return sha256_hex(
        domain_sep_bytes("fcis_m5_candidate", version=FCIS_M5_CODEC_VERSION_V1)
        + _encode_text_v1(FCIS_M5_ALGORITHM_ID_V1)
        + encode_uvarint(FCIS_M5_ALGORITHM_VERSION_V1)
        + encode_uvarint(FCIS_M5_SCHEMA_VERSION_V1)
        + encode_uvarint(FCIS_M5_CODEC_VERSION_V1)
        + _digest_bytes_v1(expected_pre_root)
        + _digest_bytes_v1(execution_context_hash)
        + _digest_bytes_v1(command_or_batch_root)
        + _digest_bytes_v1(next_state_root)
        + _encode_root_bound_payload_v1(canonical_patch)
        + _encode_root_bound_payload_v1(value_plan)
        + _encode_replay_updates_v1(replay_updates)
        + encode_bytes(outbox_material)
        + encode_bytes(receipt_body)
    )


def derive_candidate_root_v1(
    *,
    expected_pre_root: str,
    execution_context_hash: str,
    command_or_batch_root: str,
    next_state_root: str,
    canonical_patch: FCISRootBoundPayloadV1,
    value_plan: FCISRootBoundPayloadV1,
    replay_updates: tuple[FCISReplayUpdateV1, ...],
    outbox_effects: tuple[FCISOutboxEffectV1, ...],
    receipt_outcome: FCISReceiptOutcomeV1,
    receipt_code: str,
    public_reason: str,
    receipt_detail: FCISRootBoundPayloadV1 | None,
) -> str:
    return _derive_candidate_root_from_material_v1(
        expected_pre_root=expected_pre_root,
        execution_context_hash=execution_context_hash,
        command_or_batch_root=command_or_batch_root,
        next_state_root=next_state_root,
        canonical_patch=canonical_patch,
        value_plan=value_plan,
        replay_updates=replay_updates,
        outbox_material=_encode_outbox_effect_material_v1(outbox_effects),
        receipt_body=_encode_receipt_body_v1(
            outcome=receipt_outcome,
            code=receipt_code,
            public_reason=public_reason,
            detail=receipt_detail,
        ),
    )


def _derive_candidate_root_from_plan_and_receipt_v1(
    *,
    expected_pre_root: str,
    execution_context_hash: str,
    command_or_batch_root: str,
    next_state_root: str,
    plan: FCISCommitPlanV1,
    receipt: FCISReceiptV1,
) -> str:
    _validate_commit_plan_v1(plan)
    _validate_receipt_v1(receipt)
    return _derive_candidate_root_from_material_v1(
        expected_pre_root=expected_pre_root,
        execution_context_hash=execution_context_hash,
        command_or_batch_root=command_or_batch_root,
        next_state_root=next_state_root,
        canonical_patch=plan.canonical_patch,
        value_plan=plan.value_plan,
        replay_updates=plan.replay_updates,
        outbox_material=_encode_outbox_record_material_v1(plan.outbox_plan),
        receipt_body=_encode_receipt_body_v1(
            outcome=receipt.outcome,
            code=receipt.code,
            public_reason=receipt.public_reason,
            detail=receipt.detail,
        ),
    )


def validate_decision_v1(decision: FCISDecisionV1) -> None:
    if type(decision) is FCISAcceptV1:
        canonical_committed_state_bytes_v1(decision.next_state)
        _validate_commit_plan_v1(decision.commit_plan)
        _validate_receipt_v1(decision.receipt)
        if decision.receipt.outcome is not FCISReceiptOutcomeV1.ACCEPT:
            raise ValueError("accepted decision requires an accept receipt")
        if decision.receipt.candidate_root != decision.commit_plan.candidate_root:
            raise ValueError("accepted receipt and plan belong to different candidates")
        if decision.commit_plan.outbox_plan.receipt_root != receipt_root_v1(decision.receipt):
            raise ValueError("accepted outbox is not bound to its receipt")
        return
    if type(decision) is FCISRejectV1:
        require_text_v1(decision.reason, "rejection reason")
        _validate_receipt_v1(decision.rejection_receipt)
        if decision.rejection_receipt.outcome is not FCISReceiptOutcomeV1.REJECT:
            raise ValueError("ordinary reject requires a rejection receipt")
        return
    if type(decision) is FCISCommittedFailureV1:
        exact_reason = require_text_v1(decision.reason, "committed-failure reason")
        canonical_committed_state_bytes_v1(decision.next_state)
        _validate_commit_plan_v1(decision.commit_plan)
        _validate_receipt_v1(decision.receipt)
        if decision.receipt.outcome is not FCISReceiptOutcomeV1.COMMITTED_FAILURE:
            raise ValueError("committed failure requires its exact receipt variant")
        if exact_reason != decision.receipt.code:
            raise ValueError("committed-failure reason must equal the receipt code")
        if decision.receipt.candidate_root != decision.commit_plan.candidate_root:
            raise ValueError("failure receipt and plan belong to different candidates")
        if decision.commit_plan.outbox_plan.receipt_root != receipt_root_v1(decision.receipt):
            raise ValueError("failure outbox is not bound to its receipt")
        return
    raise TypeError("unknown FCIS decision variant")


def encode_decision_v1(decision: FCISDecisionV1) -> bytes:
    validate_decision_v1(decision)
    out = bytearray(domain_sep_bytes("fcis_m5_decision", version=FCIS_M5_CODEC_VERSION_V1))
    if type(decision) is FCISAcceptV1:
        out += encode_uvarint(1)
        out += _digest_bytes_v1(committed_state_root_v1(decision.next_state))
        out += _digest_bytes_v1(commit_plan_root_v1(decision.commit_plan))
        out += _digest_bytes_v1(receipt_root_v1(decision.receipt))
        return bytes(out)
    if type(decision) is FCISRejectV1:
        out += encode_uvarint(2)
        out += _encode_text_v1(decision.reason)
        out += _digest_bytes_v1(receipt_root_v1(decision.rejection_receipt))
        return bytes(out)
    if type(decision) is FCISCommittedFailureV1:
        out += encode_uvarint(3)
        out += _encode_text_v1(decision.reason)
        out += _digest_bytes_v1(committed_state_root_v1(decision.next_state))
        out += _digest_bytes_v1(commit_plan_root_v1(decision.commit_plan))
        out += _digest_bytes_v1(receipt_root_v1(decision.receipt))
        return bytes(out)
    raise AssertionError("validated decision variant disappeared")


def build_reject_decision_v1(
    *,
    code: str,
    public_reason: str,
    detail_bytes: bytes | None = None,
) -> FCISRejectV1:
    detail = (
        None
        if detail_bytes is None
        else bind_authority_payload_v1(
            FCISAuthorityPayloadDomainV1.RECEIPT_DETAIL,
            detail_bytes,
        )
    )
    receipt = FCISReceiptV1(
        outcome=FCISReceiptOutcomeV1.REJECT,
        candidate_root=None,
        code=code,
        public_reason=public_reason,
        detail=detail,
    )
    decision = FCISRejectV1(public_reason, receipt)
    validate_decision_v1(decision)
    return decision


def _build_success_decision_v1(
    *,
    outcome: FCISReceiptOutcomeV1,
    reason: str | None,
    expected_pre_root: str,
    execution_context_hash: str,
    command_or_batch_root: str,
    next_state: FCISCommittedDexStateV1,
    canonical_patch_bytes: bytes,
    value_plan_bytes: bytes,
    replay_updates: tuple[FCISReplayUpdateV1, ...],
    outbox_effects: tuple[FCISOutboxEffectV1, ...],
    receipt_code: str,
    public_reason: str,
    receipt_detail_bytes: bytes | None,
) -> FCISAcceptV1 | FCISCommittedFailureV1:
    if type(next_state) is not FCISCommittedDexStateV1:
        raise TypeError("next state must be exact")
    state_root = committed_state_root_v1(next_state)
    canonical_patch = bind_authority_payload_v1(
        FCISAuthorityPayloadDomainV1.CANONICAL_PATCH,
        canonical_patch_bytes,
    )
    value_plan = bind_authority_payload_v1(
        FCISAuthorityPayloadDomainV1.VALUE_PLAN,
        value_plan_bytes,
    )
    exact_replay_updates = require_replay_updates_v1(replay_updates)
    exact_outbox_effects = _validate_outbox_effects_v1(outbox_effects)
    detail = (
        None
        if receipt_detail_bytes is None
        else bind_authority_payload_v1(
            FCISAuthorityPayloadDomainV1.RECEIPT_DETAIL,
            receipt_detail_bytes,
        )
    )
    candidate_root = derive_candidate_root_v1(
        expected_pre_root=expected_pre_root,
        execution_context_hash=execution_context_hash,
        command_or_batch_root=command_or_batch_root,
        next_state_root=state_root,
        canonical_patch=canonical_patch,
        value_plan=value_plan,
        replay_updates=exact_replay_updates,
        outbox_effects=exact_outbox_effects,
        receipt_outcome=outcome,
        receipt_code=receipt_code,
        public_reason=public_reason,
        receipt_detail=detail,
    )
    receipt = FCISReceiptV1(
        outcome=outcome,
        candidate_root=candidate_root,
        code=receipt_code,
        public_reason=public_reason,
        detail=detail,
    )
    outbox = build_outbox_plan_v1(
        candidate_root=candidate_root,
        receipt_root=receipt_root_v1(receipt),
        effects=exact_outbox_effects,
    )
    plan = FCISCommitPlanV1(
        candidate_root=candidate_root,
        canonical_patch=canonical_patch,
        value_plan=value_plan,
        replay_updates=exact_replay_updates,
        outbox_plan=outbox,
    )
    if outcome is FCISReceiptOutcomeV1.ACCEPT:
        if reason is not None:
            raise ValueError("accept decision cannot carry a failure reason")
        decision: FCISAcceptV1 | FCISCommittedFailureV1 = FCISAcceptV1(
            next_state,
            plan,
            receipt,
        )
    elif outcome is FCISReceiptOutcomeV1.COMMITTED_FAILURE:
        exact_reason = require_text_v1(reason, "committed-failure reason")
        if exact_reason != receipt_code:
            raise ValueError("committed-failure reason must equal the receipt code")
        decision = FCISCommittedFailureV1(exact_reason, next_state, plan, receipt)
    else:
        raise ValueError("success builder cannot construct ordinary rejection")
    validate_decision_v1(decision)
    return decision


def build_accept_decision_v1(
    *,
    expected_pre_root: str,
    execution_context_hash: str,
    command_or_batch_root: str,
    next_state: FCISCommittedDexStateV1,
    canonical_patch_bytes: bytes,
    value_plan_bytes: bytes,
    replay_updates: tuple[FCISReplayUpdateV1, ...],
    outbox_effects: tuple[FCISOutboxEffectV1, ...],
    receipt_code: str = "accepted",
    public_reason: str = "accepted",
    receipt_detail_bytes: bytes | None = None,
) -> FCISAcceptV1:
    result = _build_success_decision_v1(
        outcome=FCISReceiptOutcomeV1.ACCEPT,
        reason=None,
        expected_pre_root=expected_pre_root,
        execution_context_hash=execution_context_hash,
        command_or_batch_root=command_or_batch_root,
        next_state=next_state,
        canonical_patch_bytes=canonical_patch_bytes,
        value_plan_bytes=value_plan_bytes,
        replay_updates=replay_updates,
        outbox_effects=outbox_effects,
        receipt_code=receipt_code,
        public_reason=public_reason,
        receipt_detail_bytes=receipt_detail_bytes,
    )
    if type(result) is not FCISAcceptV1:
        raise AssertionError("accept builder produced the wrong closed variant")
    return result


def build_committed_failure_decision_v1(
    *,
    reason: str,
    expected_pre_root: str,
    execution_context_hash: str,
    command_or_batch_root: str,
    next_state: FCISCommittedDexStateV1,
    canonical_patch_bytes: bytes,
    value_plan_bytes: bytes,
    replay_updates: tuple[FCISReplayUpdateV1, ...],
    outbox_effects: tuple[FCISOutboxEffectV1, ...],
    receipt_code: str,
    public_reason: str,
    receipt_detail_bytes: bytes | None = None,
) -> FCISCommittedFailureV1:
    result = _build_success_decision_v1(
        outcome=FCISReceiptOutcomeV1.COMMITTED_FAILURE,
        reason=reason,
        expected_pre_root=expected_pre_root,
        execution_context_hash=execution_context_hash,
        command_or_batch_root=command_or_batch_root,
        next_state=next_state,
        canonical_patch_bytes=canonical_patch_bytes,
        value_plan_bytes=value_plan_bytes,
        replay_updates=replay_updates,
        outbox_effects=outbox_effects,
        receipt_code=receipt_code,
        public_reason=public_reason,
        receipt_detail_bytes=receipt_detail_bytes,
    )
    if type(result) is not FCISCommittedFailureV1:
        raise AssertionError("failure builder produced the wrong closed variant")
    return result


def validate_commit_bundle_v1(bundle: FCISCommitBundleV1) -> None:
    if type(bundle) is not FCISCommitBundleV1:
        raise TypeError("commit bundle must be exact")
    require_digest_v1(bundle.expected_pre_root, "bundle expected pre-root")
    require_digest_v1(bundle.execution_context_hash, "bundle context hash")
    require_digest_v1(bundle.command_or_batch_root, "bundle command root")
    if bundle.algorithm_id != FCIS_M5_ALGORITHM_ID_V1:
        raise ValueError("unexpected M5 algorithm id")
    if bundle.algorithm_version != FCIS_M5_ALGORITHM_VERSION_V1:
        raise ValueError("unexpected M5 algorithm version")
    if bundle.schema_version != FCIS_M5_SCHEMA_VERSION_V1:
        raise ValueError("unexpected M5 schema version")
    if bundle.codec_version != FCIS_M5_CODEC_VERSION_V1:
        raise ValueError("unexpected M5 codec version")
    next_root = committed_state_root_v1(bundle.next_state)
    require_digest_v1(bundle.next_state_root, "bundle next-state root")
    if bundle.next_state_root != next_root:
        raise ValueError("bundle next-state root mismatch")
    _validate_commit_plan_v1(bundle.commit_plan)
    _validate_receipt_v1(bundle.receipt)
    if bundle.receipt.outcome is FCISReceiptOutcomeV1.REJECT:
        raise ValueError("ordinary rejection cannot produce a commit bundle")
    require_digest_v1(bundle.commit_plan_root, "bundle commit-plan root")
    if bundle.commit_plan_root != commit_plan_root_v1(bundle.commit_plan):
        raise ValueError("bundle commit-plan root mismatch")
    require_digest_v1(bundle.receipt_root, "bundle receipt root")
    if bundle.receipt_root != receipt_root_v1(bundle.receipt):
        raise ValueError("bundle receipt root mismatch")
    _validate_root_bound_payload_v1(
        bundle.canonical_patch,
        expected_domain=FCISAuthorityPayloadDomainV1.CANONICAL_PATCH,
    )
    if bundle.canonical_patch != bundle.commit_plan.canonical_patch:
        raise ValueError("bundle patch and commit-plan patch differ")
    require_replay_updates_v1(bundle.replay_updates)
    if bundle.replay_updates != bundle.commit_plan.replay_updates:
        raise ValueError("bundle replay updates and commit-plan updates differ")
    _validate_outbox_plan_v1(
        bundle.outbox_plan,
        expected_candidate_root=bundle.commit_plan.candidate_root,
        expected_receipt_root=bundle.receipt_root,
    )
    if bundle.outbox_plan != bundle.commit_plan.outbox_plan:
        raise ValueError("bundle outbox and commit-plan outbox differ")
    candidate_root = _derive_candidate_root_from_plan_and_receipt_v1(
        expected_pre_root=bundle.expected_pre_root,
        execution_context_hash=bundle.execution_context_hash,
        command_or_batch_root=bundle.command_or_batch_root,
        next_state_root=bundle.next_state_root,
        plan=bundle.commit_plan,
        receipt=bundle.receipt,
    )
    if bundle.commit_plan.candidate_root != candidate_root:
        raise ValueError("bundle plan belongs to a different candidate")
    if bundle.receipt.candidate_root != candidate_root:
        raise ValueError("bundle receipt belongs to a different candidate")
    if bundle.outbox_plan.candidate_root != candidate_root:
        raise ValueError("bundle outbox belongs to a different candidate")


def build_commit_bundle_v1(
    *,
    expected_pre_root: str,
    execution_context_hash: str,
    command_or_batch_root: str,
    decision: FCISDecisionV1,
) -> FCISCommitBundleV1:
    validate_decision_v1(decision)
    if type(decision) is FCISRejectV1:
        raise ValueError("ordinary rejection cannot produce a commit bundle")
    if type(decision) not in (FCISAcceptV1, FCISCommittedFailureV1):
        raise TypeError("unknown FCIS decision variant")
    plan = decision.commit_plan
    receipt = decision.receipt
    state = decision.next_state
    return FCISCommitBundleV1(
        expected_pre_root=require_digest_v1(expected_pre_root, "expected pre-root"),
        execution_context_hash=require_digest_v1(
            execution_context_hash,
            "execution-context hash",
        ),
        command_or_batch_root=require_digest_v1(command_or_batch_root, "command root"),
        algorithm_id=FCIS_M5_ALGORITHM_ID_V1,
        algorithm_version=FCIS_M5_ALGORITHM_VERSION_V1,
        schema_version=FCIS_M5_SCHEMA_VERSION_V1,
        codec_version=FCIS_M5_CODEC_VERSION_V1,
        next_state=state,
        next_state_root=committed_state_root_v1(state),
        canonical_patch=plan.canonical_patch,
        commit_plan=plan,
        commit_plan_root=commit_plan_root_v1(plan),
        receipt=receipt,
        receipt_root=receipt_root_v1(receipt),
        replay_updates=plan.replay_updates,
        outbox_plan=plan.outbox_plan,
    )


def encode_commit_bundle_v1(bundle: FCISCommitBundleV1) -> bytes:
    validate_commit_bundle_v1(bundle)
    return (
        domain_sep_bytes("fcis_m5_commit_bundle", version=FCIS_M5_CODEC_VERSION_V1)
        + _digest_bytes_v1(bundle.expected_pre_root)
        + _digest_bytes_v1(bundle.execution_context_hash)
        + _digest_bytes_v1(bundle.command_or_batch_root)
        + _encode_text_v1(bundle.algorithm_id)
        + encode_uvarint(bundle.algorithm_version)
        + encode_uvarint(bundle.schema_version)
        + encode_uvarint(bundle.codec_version)
        + _digest_bytes_v1(bundle.next_state_root)
        + _encode_root_bound_payload_v1(bundle.canonical_patch)
        + encode_bytes(encode_commit_plan_v1(bundle.commit_plan))
        + _digest_bytes_v1(bundle.commit_plan_root)
        + encode_bytes(encode_receipt_v1(bundle.receipt))
        + _digest_bytes_v1(bundle.receipt_root)
        + _encode_replay_updates_v1(bundle.replay_updates)
        + _encode_outbox_plan_v1(bundle.outbox_plan)
    )


def commit_bundle_root_v1(bundle: FCISCommitBundleV1) -> str:
    return sha256_hex(encode_commit_bundle_v1(bundle))


__all__ = (
    "bind_authority_payload_v1",
    "build_accept_decision_v1",
    "build_commit_bundle_v1",
    "build_committed_failure_decision_v1",
    "build_outbox_plan_v1",
    "build_reject_decision_v1",
    "canonical_committed_state_bytes_v1",
    "commit_bundle_root_v1",
    "commit_plan_root_v1",
    "committed_state_root_v1",
    "derive_candidate_root_v1",
    "encode_commit_bundle_v1",
    "encode_commit_plan_v1",
    "encode_decision_v1",
    "encode_receipt_v1",
    "outbox_idempotency_key_v1",
    "receipt_root_v1",
    "root_bound_payload_digest_v1",
    "validate_commit_bundle_v1",
    "validate_decision_v1",
)
