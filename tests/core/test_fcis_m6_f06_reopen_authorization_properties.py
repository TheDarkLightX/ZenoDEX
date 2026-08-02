"""Property-style F06 token mutation tests."""

from __future__ import annotations

import hypothesis.strategies as st
from hypothesis import given, settings

from experiments.fcis_m6_f03_reopen_check import build_layout
from experiments.fcis_m6_f06_reopen_authorization_check import (
    AcceptingVerifier,
    build_evidence,
    build_genesis,
)
from src.core.fcis_durable_retraction import tagged_digest
from src.core.fcis_m6_f03_reopen import F03ReopenSuccessV1, reopen_layout
from src.core.fcis_m6_f06_reopen_authorization import (
    F06AuthorizationCodeV1,
    F06AuthorizationRejectV1,
    F06AuthorizationTokenV1,
    F06OperationV1,
    issue_f06_reopen_token,
    require_f06_token_at_use,
)

_LABELS = st.text(
    alphabet=st.characters(
        whitelist_categories=("Ll", "Lu", "Nd"),
        whitelist_characters="_-",
    ),
    min_size=1,
    max_size=32,
)


@settings(max_examples=24, deadline=None, derandomize=True)  # type: ignore[untyped-decorator]
@given(label=_LABELS)  # type: ignore[untyped-decorator]
def test_generated_token_root_substitutions_fail_at_use(label: str) -> None:
    layout = build_layout()
    reopened = reopen_layout(layout)
    assert type(reopened) is F03ReopenSuccessV1
    genesis = build_genesis(layout)
    external_root = "0x" + "a" * 64
    evidence = build_evidence(reopened, external_authorization_root=external_root)
    verifier = AcceptingVerifier()
    issued = issue_f06_reopen_token(
        reopened,
        genesis=genesis,
        external_authorization_root=external_root,
        evidence=evidence,
        verifier_adapter=verifier,
        current_epoch=3,
    )
    assert type(issued) is F06AuthorizationTokenV1
    forged = object.__new__(type(issued))
    object.__setattr__(forged, "head", issued.head)
    object.__setattr__(forged, "evidence", issued.evidence)
    object.__setattr__(forged, "token_root", f"0x{tagged_digest(f'f06/property/{label}')}")

    result = require_f06_token_at_use(
        reopened,
        genesis=genesis,
        token=forged,
        operation=F06OperationV1.COMMIT,
        verifier_adapter=verifier,
        current_epoch=3,
    )

    assert type(result) is F06AuthorizationRejectV1
    assert result.code is F06AuthorizationCodeV1.TOKEN_REJECTED
