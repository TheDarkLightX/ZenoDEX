"""Deterministic D07 checker for RQAG stutter receipts."""

from __future__ import annotations

import json
import sys
from hashlib import sha256
from pathlib import Path
from typing import Callable, cast

_ROOT = Path(__file__).resolve().parents[1]
if str(_ROOT) not in sys.path:
    sys.path.insert(0, str(_ROOT))

from src.core.fcis_stutter_receipt import (  # noqa: E402
    NonStutterOperationKindV1,
    StutterCheckerIdV1,
    StutterOperationKindV1,
    StutterReceiptV1,
    StutterRejectCodeV1,
    StutterRejectV1,
    verify_stutter_candidate_v1,
    verify_stutter_receipt_v1,
)

_VECTOR_PATH = _ROOT / "docs/research/m6_tasks/TASK_D07_STUTTER_RECEIPT_VECTOR.json"


def _root(label: str) -> str:
    return f"0x{sha256(label.encode('utf-8')).hexdigest()}"


def _read_vector() -> dict[str, object]:
    value = json.loads(_VECTOR_PATH.read_text(encoding="utf-8"))
    if type(value) is not dict:
        raise AssertionError("D07 vector must be an object")
    return cast(dict[str, object], value)


def _expect_code(
    label: str,
    expected_code: StutterRejectCodeV1,
    result: object,
) -> None:
    if type(result) is not StutterRejectV1:
        raise AssertionError(f"{label} unexpectedly produced a receipt")
    if result.code is not expected_code:
        raise AssertionError(f"{label} produced {result.code.value}")


def _expect_rejection(
    label: str,
    expected_code: StutterRejectCodeV1,
    callback: Callable[[], object],
) -> None:
    _expect_code(label, expected_code, callback())


def run_checks() -> None:
    vector = _read_vector()
    if vector.get("schema_version") != "zenodex.fcis.m6.d07.stutter-receipt-vector.v1":
        raise AssertionError("D07 vector has the wrong schema")
    eligible = vector.get("eligible_operations")
    if type(eligible) is not list or len(eligible) != len(tuple(StutterOperationKindV1)):
        raise AssertionError("D07 vector does not cover every eligible operation")
    expected_rows: list[dict[str, object]] = []
    for operation_kind in StutterOperationKindV1:
        operation_id = _root(f"operation:{operation_kind.value}")
        canonical_root = _root("canonical:stable")
        observable_root = _root("observable:stable")
        result = verify_stutter_candidate_v1(
            operation_id=operation_id,
            operation_kind=operation_kind,
            pre_canonical_root=canonical_root,
            post_canonical_root=canonical_root,
            observable_pre_root=observable_root,
            observable_post_root=observable_root,
        )
        if type(result) is not StutterReceiptV1:
            raise AssertionError(f"{operation_kind.value} did not produce a receipt")
        if verify_stutter_receipt_v1(result) is not result:
            raise AssertionError(f"{operation_kind.value} did not revalidate")
        expected_rows.append(
            {
                "operation_id": operation_id,
                "operation_kind": operation_kind.value,
                "pre_canonical_root": canonical_root,
                "post_canonical_root": canonical_root,
                "observable_root": observable_root,
                "checker_id": result.checker_id.value,
                "verification_root": result.verification_root,
                "receipt_root": result.receipt_root,
            }
        )
    if eligible != expected_rows:
        raise AssertionError("D07 vector does not match regenerated receipt outputs")

    forbidden = vector.get("forbidden_operations")
    expected_forbidden = [operation.value for operation in NonStutterOperationKindV1]
    if forbidden != expected_forbidden:
        raise AssertionError("D07 vector does not enumerate forbidden operations")
    for forbidden_kind in NonStutterOperationKindV1:
        result = verify_stutter_candidate_v1(
            operation_id=_root("forbidden-operation"),
            operation_kind=forbidden_kind,
            pre_canonical_root=_root("canonical:stable"),
            post_canonical_root=_root("canonical:stable"),
            observable_pre_root=_root("observable:stable"),
            observable_post_root=_root("observable:stable"),
        )
        _expect_code(
            forbidden_kind.value,
            StutterRejectCodeV1.FORBIDDEN_OPERATION,
            result,
        )

    expected_rejections = vector.get("expected_rejections")
    if type(expected_rejections) is not dict:
        raise AssertionError("D07 expected rejections must be an object")
    rejection_map = cast(dict[str, object], expected_rejections)
    if rejection_map.get("forbidden_operation") != StutterRejectCodeV1.FORBIDDEN_OPERATION.value:
        raise AssertionError("D07 forbidden rejection code drifted")

    _expect_rejection(
        "canonical state change",
        StutterRejectCodeV1.CANONICAL_STATE_CHANGED,
        lambda: verify_stutter_candidate_v1(
            operation_id=_root("new-commit"),
            operation_kind=StutterOperationKindV1.SAME_COMMIT_RETRY,
            pre_canonical_root=_root("canonical:pre"),
            post_canonical_root=_root("canonical:post"),
            observable_pre_root=_root("observable:same"),
            observable_post_root=_root("observable:same"),
        ),
    )
    _expect_rejection(
        "observable state change",
        StutterRejectCodeV1.OBSERVABLE_STATE_CHANGED,
        lambda: verify_stutter_candidate_v1(
            operation_id=_root("effect-redelivery"),
            operation_kind=StutterOperationKindV1.SAME_EFFECT_DESTINATION_DEDUP,
            pre_canonical_root=_root("canonical:same"),
            post_canonical_root=_root("canonical:same"),
            observable_pre_root=_root("observable:pre"),
            observable_post_root=_root("observable:post"),
        ),
    )
    _expect_rejection(
        "wrong operation kind",
        StutterRejectCodeV1.WRONG_EXACT_TYPE,
        lambda: verify_stutter_candidate_v1(
            operation_id=_root("wrong-kind"),
            operation_kind="new_commit",
            pre_canonical_root=_root("canonical"),
            post_canonical_root=_root("canonical"),
            observable_pre_root=_root("observable"),
            observable_post_root=_root("observable"),
        ),
    )
    _expect_rejection(
        "invalid operation root",
        StutterRejectCodeV1.INVALID_ROOT,
        lambda: verify_stutter_candidate_v1(
            operation_id="not-a-root",
            operation_kind=StutterOperationKindV1.REPEAT_PURE_VERIFICATION,
            pre_canonical_root=_root("canonical"),
            post_canonical_root=_root("canonical"),
            observable_pre_root=_root("observable"),
            observable_post_root=_root("observable"),
        ),
    )

    receipt_result = verify_stutter_candidate_v1(
        operation_id=_root("tamper"),
        operation_kind=StutterOperationKindV1.SAME_COMMIT_RETRY,
        pre_canonical_root=_root("canonical:stable"),
        post_canonical_root=_root("canonical:stable"),
        observable_pre_root=_root("observable:stable"),
        observable_post_root=_root("observable:stable"),
    )
    if type(receipt_result) is not StutterReceiptV1:
        raise AssertionError("tamper baseline did not produce a receipt")
    object.__setattr__(
        receipt_result,
        "checker_id",
        type(receipt_result.checker_id).REPEAT_PURE_VERIFICATION,
    )
    _expect_code(
        "checker substitution",
        StutterRejectCodeV1.CHECKER_MISMATCH,
        verify_stutter_receipt_v1(receipt_result),
    )

    verification_result = verify_stutter_candidate_v1(
        operation_id=_root("verification-tamper"),
        operation_kind=StutterOperationKindV1.REPEAT_PURE_VERIFICATION,
        pre_canonical_root=_root("canonical:stable"),
        post_canonical_root=_root("canonical:stable"),
        observable_pre_root=_root("observable:stable"),
        observable_post_root=_root("observable:stable"),
    )
    if type(verification_result) is not StutterReceiptV1:
        raise AssertionError("verification-tamper baseline did not produce a receipt")
    object.__setattr__(verification_result, "verification_root", _root("forged-proof"))
    _expect_code(
        "verification root substitution",
        StutterRejectCodeV1.INVALID_RECEIPT,
        verify_stutter_receipt_v1(verification_result),
    )

    def _direct_constructor() -> object:
        root = _root("direct-construction")
        return StutterReceiptV1(
            operation_id=root,
            operation_kind=StutterOperationKindV1.SAME_COMMIT_RETRY,
            pre_canonical_root=root,
            post_canonical_root=root,
            observable_root=root,
            checker_id=StutterCheckerIdV1.SAME_COMMIT_RETRY,
            verification_root=root,
            _construction_token=object(),
        )

    try:
        _direct_constructor()
    except TypeError as exc:
        if "controlled verification" not in str(exc):
            raise AssertionError("direct construction had an unexpected failure") from exc
    else:
        raise AssertionError("direct receipt construction was accepted")


if __name__ == "__main__":
    run_checks()
    print("D07_STUTTER_RECEIPT_MATCH")
