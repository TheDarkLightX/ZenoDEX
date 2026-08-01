from __future__ import annotations

from hashlib import sha256

import pytest

from src.core.fcis_stutter_receipt import (
    NonStutterOperationKindV1,
    StutterCheckerIdV1,
    StutterOperationKindV1,
    StutterReceiptV1,
    StutterRejectCodeV1,
    StutterRejectV1,
    verify_stutter_candidate_v1,
    verify_stutter_receipt_v1,
)


def _root(label: str) -> str:
    return f"0x{sha256(label.encode('utf-8')).hexdigest()}"


def _receipt(
    operation_kind: StutterOperationKindV1 = StutterOperationKindV1.SAME_COMMIT_RETRY,
) -> StutterReceiptV1:
    result = verify_stutter_candidate_v1(
        operation_id=_root(f"operation:{operation_kind.value}"),
        operation_kind=operation_kind,
        pre_canonical_root=_root("canonical:stable"),
        post_canonical_root=_root("canonical:stable"),
        observable_pre_root=_root("observable:stable"),
        observable_post_root=_root("observable:stable"),
    )
    assert type(result) is StutterReceiptV1
    return result


def test_each_eligible_operation_yields_a_revalidatable_receipt() -> None:
    for operation_kind in StutterOperationKindV1:
        receipt = _receipt(operation_kind)
        assert receipt.pre_canonical_root == receipt.post_canonical_root
        assert receipt.checker_id is StutterCheckerIdV1[operation_kind.name]
        assert receipt.receipt_root.startswith("0x")
        assert verify_stutter_receipt_v1(receipt) is receipt


def test_new_commit_ack_and_migration_are_forbidden_stutters() -> None:
    for operation_kind in NonStutterOperationKindV1:
        result = verify_stutter_candidate_v1(
            operation_id=_root("forbidden-operation"),
            operation_kind=operation_kind,
            pre_canonical_root=_root("canonical:stable"),
            post_canonical_root=_root("canonical:stable"),
            observable_pre_root=_root("observable:stable"),
            observable_post_root=_root("observable:stable"),
        )
        assert type(result) is StutterRejectV1
        assert result.code is StutterRejectCodeV1.FORBIDDEN_OPERATION


def test_canonical_state_change_rejects_even_with_same_observable_root() -> None:
    result = verify_stutter_candidate_v1(
        operation_id=_root("new-commit"),
        operation_kind=StutterOperationKindV1.SAME_COMMIT_RETRY,
        pre_canonical_root=_root("canonical:pre"),
        post_canonical_root=_root("canonical:post"),
        observable_pre_root=_root("observable:same"),
        observable_post_root=_root("observable:same"),
    )
    assert type(result) is StutterRejectV1
    assert result.code is StutterRejectCodeV1.CANONICAL_STATE_CHANGED


def test_observable_state_change_rejects_with_same_canonical_root() -> None:
    result = verify_stutter_candidate_v1(
        operation_id=_root("effect-redelivery"),
        operation_kind=StutterOperationKindV1.SAME_EFFECT_DESTINATION_DEDUP,
        pre_canonical_root=_root("canonical:same"),
        post_canonical_root=_root("canonical:same"),
        observable_pre_root=_root("observable:pre"),
        observable_post_root=_root("observable:post"),
    )
    assert type(result) is StutterRejectV1
    assert result.code is StutterRejectCodeV1.OBSERVABLE_STATE_CHANGED


def test_wrong_operation_variant_and_roots_fail_closed() -> None:
    wrong_kind = verify_stutter_candidate_v1(
        operation_id=_root("wrong-kind"),
        operation_kind="new_commit",
        pre_canonical_root=_root("canonical"),
        post_canonical_root=_root("canonical"),
        observable_pre_root=_root("observable"),
        observable_post_root=_root("observable"),
    )
    assert type(wrong_kind) is StutterRejectV1
    assert wrong_kind.code is StutterRejectCodeV1.WRONG_EXACT_TYPE

    wrong_root = verify_stutter_candidate_v1(
        operation_id="not-a-root",
        operation_kind=StutterOperationKindV1.REPEAT_PURE_VERIFICATION,
        pre_canonical_root=_root("canonical"),
        post_canonical_root=_root("canonical"),
        observable_pre_root=_root("observable"),
        observable_post_root=_root("observable"),
    )
    assert type(wrong_root) is StutterRejectV1
    assert wrong_root.code is StutterRejectCodeV1.INVALID_ROOT


def test_direct_receipt_construction_is_controlled() -> None:
    root = _root("controlled")
    with pytest.raises(TypeError, match="controlled verification"):
        StutterReceiptV1(
            operation_id=root,
            operation_kind=StutterOperationKindV1.SAME_COMMIT_RETRY,
            pre_canonical_root=root,
            post_canonical_root=root,
            observable_root=root,
            checker_id=StutterCheckerIdV1.SAME_COMMIT_RETRY,
            verification_root=root,
            _construction_token=object(),
        )


def test_tampered_checker_is_reported_as_checker_mismatch() -> None:
    receipt = _receipt()
    object.__setattr__(receipt, "checker_id", StutterCheckerIdV1.REPEAT_PURE_VERIFICATION)
    result = verify_stutter_receipt_v1(receipt)
    assert type(result) is StutterRejectV1
    assert result.code is StutterRejectCodeV1.CHECKER_MISMATCH


def test_tampered_verification_root_is_rejected() -> None:
    receipt = _receipt()
    object.__setattr__(receipt, "verification_root", _root("forged-proof"))
    result = verify_stutter_receipt_v1(receipt)
    assert type(result) is StutterRejectV1
    assert result.code is StutterRejectCodeV1.INVALID_RECEIPT


def test_wrong_receipt_type_is_rejected() -> None:
    result = verify_stutter_receipt_v1(object())
    assert type(result) is StutterRejectV1
    assert result.code is StutterRejectCodeV1.WRONG_EXACT_TYPE
