"""Focused F06 fresh reopen-head authorization tests."""

from __future__ import annotations

from experiments.fcis_m6_f03_reopen_check import build_layout
from experiments.fcis_m6_f06_reopen_authorization_check import (
    AcceptingVerifier,
    build_evidence,
    build_genesis,
)
from src.core.fcis_m6_f03_reopen import F03ReopenSuccessV1, reopen_layout
from src.core.fcis_m6_f06_reopen_authorization import (
    F06AuthorizationCodeV1,
    F06AuthorizationRejectV1,
    F06AuthorizationTokenV1,
    F06AuthorizationUseV1,
    F06OperationV1,
    issue_f06_reopen_token,
    require_f06_token_at_use,
)


def _token() -> tuple[object, object, F06AuthorizationTokenV1, AcceptingVerifier]:
    layout = build_layout()
    reopened = reopen_layout(layout)
    assert type(reopened) is F03ReopenSuccessV1
    genesis = build_genesis(layout)
    external_root = "0x" + "a" * 64
    evidence = build_evidence(reopened, external_authorization_root=external_root)
    verifier = AcceptingVerifier()
    token = issue_f06_reopen_token(
        reopened,
        genesis=genesis,
        external_authorization_root=external_root,
        evidence=evidence,
        verifier_adapter=verifier,
        current_epoch=3,
    )
    assert type(token) is F06AuthorizationTokenV1
    return reopened, genesis, token, verifier


def test_issue_requires_external_verifier_and_use_rechecks_each_operation() -> None:
    reopened, genesis, token, verifier = _token()

    for operation in F06OperationV1:
        result = require_f06_token_at_use(
            reopened,
            genesis=genesis,
            token=token,
            operation=operation,
            verifier_adapter=verifier,
            current_epoch=3,
        )
        assert type(result) is F06AuthorizationUseV1
    assert verifier.calls == 4


def test_wrong_operation_and_wrong_exact_token_are_typed_rejections() -> None:
    reopened, genesis, token, verifier = _token()
    forged = object.__new__(type(token))
    object.__setattr__(forged, "head", token.head)
    object.__setattr__(forged, "evidence", token.evidence)
    object.__setattr__(forged, "token_root", "0x" + "b" * 64)

    wrong_operation = require_f06_token_at_use(
        reopened,
        genesis=genesis,
        token=token,
        operation=object(),
        verifier_adapter=verifier,
        current_epoch=3,
    )
    forged_result = require_f06_token_at_use(
        reopened,
        genesis=genesis,
        token=forged,
        operation=F06OperationV1.COMMIT,
        verifier_adapter=verifier,
        current_epoch=3,
    )

    assert type(wrong_operation) is F06AuthorizationRejectV1
    assert wrong_operation.code is F06AuthorizationCodeV1.INVALID_OPERATION
    assert type(forged_result) is F06AuthorizationRejectV1
    assert forged_result.code is F06AuthorizationCodeV1.TOKEN_REJECTED
