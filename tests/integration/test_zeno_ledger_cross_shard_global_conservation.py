from __future__ import annotations

from copy import deepcopy

from src.core.cross_shard_ledger_posting import (
    CrossShardLedgerPostingBuildResult,
    CrossShardLedgerPostingSummaryV1,
)
from src.integration.zeno_ledger_cross_shard_effect_application import (
    build_cross_shard_ledger_effects_artifact_v0,
    empty_cross_shard_applied_effects_state_v0,
)
from src.integration.zeno_ledger_cross_shard_global_conservation import (
    build_cross_shard_global_conservation_receipt_v0,
    validate_cross_shard_global_conservation_receipt_v0,
    verify_cross_shard_global_conservation_receipt_v0,
)
from src.integration.zeno_ledger_tau_export import (
    build_cross_shard_posting_summary_export_v0,
)
from src.integration.zeno_ledger_v0 import hash_v0

_SETTLEMENT_CERT_HASH = "0x" + "c" * 64


def _posting_summary(*, quote_atoms: int = 1_000, base_atoms: int = 250) -> dict[str, object]:
    postings = (
        CrossShardLedgerPostingSummaryV1(
            asset_id="base",
            committed_debit_atoms=base_atoms,
            committed_credit_atoms=base_atoms,
        ),
        CrossShardLedgerPostingSummaryV1(
            asset_id="quote",
            committed_debit_atoms=quote_atoms,
            committed_credit_atoms=quote_atoms,
        ),
    )
    result = CrossShardLedgerPostingBuildResult(
        ok=True,
        error=None,
        sharded_settlement_certificate_hash=_SETTLEMENT_CERT_HASH,
        postings=postings,
        total_committed_debit_atoms=quote_atoms + base_atoms,
        total_committed_credit_atoms=quote_atoms + base_atoms,
    )
    return build_cross_shard_posting_summary_export_v0(posting_result=result)


def _receipt_inputs() -> tuple[dict[str, object], dict[str, object], object, object]:
    posting = _posting_summary()
    artifact = build_cross_shard_ledger_effects_artifact_v0(posting_summary=posting)
    pre = empty_cross_shard_applied_effects_state_v0()
    post = pre.add(str(artifact["ledger_effects_hash"]))
    return posting, artifact, pre, post


def test_global_conservation_receipt_binds_posting_effects_and_replay_roots() -> None:
    posting, artifact, pre, post = _receipt_inputs()

    receipt = build_cross_shard_global_conservation_receipt_v0(
        posting_summary=posting,
        effects_artifact=artifact,
        pre_replay_state=pre,
        post_replay_state=post,
        sharded_settlement_certificate_hash=_SETTLEMENT_CERT_HASH,
    )
    verdict = verify_cross_shard_global_conservation_receipt_v0(
        receipt=receipt,
        posting_summary=posting,
        effects_artifact=artifact,
        pre_replay_state=pre,
        post_replay_state=post,
        sharded_settlement_certificate_hash=_SETTLEMENT_CERT_HASH,
    )

    assert verdict.ok is True
    assert verdict.error is None
    assert validate_cross_shard_global_conservation_receipt_v0(receipt) == receipt
    assert receipt["status"] == "verified_global_conservation"
    assert receipt["sharded_settlement_certificate_hash"] == _SETTLEMENT_CERT_HASH
    assert receipt["posting_summary_hash"] == posting["posting_summary_hash"]
    assert receipt["ledger_effects_hash"] == artifact["ledger_effects_hash"]
    assert receipt["pre_replay_state_root"] == pre.root_hash()
    assert receipt["post_replay_state_root"] == post.root_hash()
    assert receipt["total_debit_atoms"] == 1_250
    assert receipt["total_credit_atoms"] == 1_250
    assert receipt["asset_rows"] == [
        {
            "asset_id": "base",
            "posting_debit_atoms": 250,
            "posting_credit_atoms": 250,
            "effect_debit_atoms": 250,
            "effect_credit_atoms": 250,
        },
        {
            "asset_id": "quote",
            "posting_debit_atoms": 1_000,
            "posting_credit_atoms": 1_000,
            "effect_debit_atoms": 1_000,
            "effect_credit_atoms": 1_000,
        },
    ]


def test_global_conservation_receipt_rejects_independently_valid_source_mismatch() -> None:
    posting, _artifact, pre, _post = _receipt_inputs()
    other_posting = _posting_summary(quote_atoms=900, base_atoms=250)
    other_artifact = build_cross_shard_ledger_effects_artifact_v0(
        posting_summary=other_posting
    )
    post = pre.add(str(other_artifact["ledger_effects_hash"]))

    verdict = verify_cross_shard_global_conservation_receipt_v0(
        receipt=build_cross_shard_global_conservation_receipt_v0(
            posting_summary=other_posting,
            effects_artifact=other_artifact,
            pre_replay_state=pre,
            post_replay_state=post,
        ),
        posting_summary=posting,
        effects_artifact=other_artifact,
        pre_replay_state=pre,
        post_replay_state=post,
    )

    assert verdict.ok is False
    assert verdict.error == "cross-shard effects are not sourced from posting summary"


def test_global_conservation_receipt_rejects_settlement_source_mismatch() -> None:
    posting, artifact, pre, post = _receipt_inputs()

    try:
        build_cross_shard_global_conservation_receipt_v0(
            posting_summary=posting,
            effects_artifact=artifact,
            pre_replay_state=pre,
            post_replay_state=post,
            sharded_settlement_certificate_hash="0x" + "d" * 64,
        )
    except ValueError as exc:
        assert str(exc) == "receipt settlement hash does not match posting summary source"
        return
    raise AssertionError("expected stale settlement source to reject")


def test_global_conservation_receipt_rejects_missing_replay_advance() -> None:
    posting, artifact, pre, _post = _receipt_inputs()

    try:
        build_cross_shard_global_conservation_receipt_v0(
            posting_summary=posting,
            effects_artifact=artifact,
            pre_replay_state=pre,
            post_replay_state=pre,
        )
    except ValueError as exc:
        assert str(exc) == "post replay state must equal pre replay state plus ledger effects hash"
        return
    raise AssertionError("expected missing replay advance to reject")


def test_global_conservation_receipt_rejects_replay_hash_already_in_pre_state() -> None:
    posting, artifact, _pre, post = _receipt_inputs()

    try:
        build_cross_shard_global_conservation_receipt_v0(
            posting_summary=posting,
            effects_artifact=artifact,
            pre_replay_state=post,
            post_replay_state=post,
        )
    except ValueError as exc:
        assert str(exc) == "cross-shard ledger effects already present in pre replay state"
        return
    raise AssertionError("expected pre-state replay to reject")


def test_global_conservation_receipt_rejects_extra_post_replay_hash() -> None:
    posting, artifact, pre, post = _receipt_inputs()
    extra_post = post.add(hash_v0("test", {"extra": 1}))

    try:
        build_cross_shard_global_conservation_receipt_v0(
            posting_summary=posting,
            effects_artifact=artifact,
            pre_replay_state=pre,
            post_replay_state=extra_post,
        )
    except ValueError as exc:
        assert str(exc) == "post replay state must equal pre replay state plus ledger effects hash"
        return
    raise AssertionError("expected extra post replay hash to reject")


def test_global_conservation_receipt_rejects_tampered_receipt_hash() -> None:
    posting, artifact, pre, post = _receipt_inputs()
    receipt = build_cross_shard_global_conservation_receipt_v0(
        posting_summary=posting,
        effects_artifact=artifact,
        pre_replay_state=pre,
        post_replay_state=post,
    )
    tampered = deepcopy(receipt)
    tampered["total_credit_atoms"] = 1_249

    try:
        validate_cross_shard_global_conservation_receipt_v0(tampered)
    except ValueError as exc:
        assert str(exc) == "cross-shard global conservation receipt totals must balance"
        return
    raise AssertionError("expected tampered receipt to reject")
