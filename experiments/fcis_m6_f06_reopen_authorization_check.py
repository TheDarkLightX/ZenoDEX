"""Independent checker and vector builder for F06 reopen authorization."""

from __future__ import annotations

import json
from dataclasses import replace
from pathlib import Path
from typing import cast

from experiments.fcis_m6_f02_history_encoder_check import build_history
from experiments.fcis_m6_f03_reopen_check import build_layout
from src.core.fcis_durable_retraction import tagged_digest
from src.core.fcis_m6_f01_history_atom import FCIS_M6_F01_HISTORY_ATOM_SCHEMA_V1
from src.core.fcis_m6_f02_history_encoder import F02DurableLayoutV1, encode_history
from src.core.fcis_m6_f03_reopen import F03ReopenSuccessV1, reopen_layout
from src.core.fcis_m6_f05_authenticated_genesis import (
    F05GenesisV1,
    build_f05_genesis_v1,
)
from src.core.fcis_m6_f06_reopen_authorization import (
    FCIS_M6_F06_REOPEN_AUTHORIZATION_SCHEMA_V1,
    F06AuthorizationCodeV1,
    F06AuthorizationRejectV1,
    F06AuthorizationTokenV1,
    F06AuthorizationUseV1,
    F06ExternalAuthorizationEvidenceV1,
    F06OperationV1,
    derive_f06_evidence_root_v1,
    issue_f06_reopen_token,
    require_f06_token_at_use,
)
from src.state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex

ROOT = Path(__file__).resolve().parents[1]
VECTOR_PATH = ROOT / "docs/research/m6_tasks/TASK_F06_REOPEN_AUTHORIZATION_V1.json"
PROOF_POLICY_ID = "zenodex/fcis/proof-context/v1"
MIGRATION_POLICY_ID = "zenodex/fcis/m6/migration-policy/v1"


def _root(label: str) -> str:
    return f"0x{tagged_digest(f'f06/{label}')}"


def build_genesis(layout: F02DurableLayoutV1) -> F05GenesisV1:
    return build_f05_genesis_v1(
        chain_id="zenodex/f06-chain",
        deployment_id="zenodex/f06-deployment",
        initial_state_root=layout.header.genesis_state_root,
        initial_configuration_root=layout.header.deployment_config_root,
        initial_authority_profile_id="zenodex/fcis/m6/authority/f06-genesis-v1",
        initial_authority_profile_root=layout.authority_rows[0].authority_state_root,
        history_schema=FCIS_M6_F01_HISTORY_ATOM_SCHEMA_V1,
        proof_context_policy_id=PROOF_POLICY_ID,
        proof_context_policy_root=_root("proof-policy"),
        migration_policy_id=MIGRATION_POLICY_ID,
        migration_policy_root=_root("migration-policy"),
    )


def _evidence_root(payload: dict[str, object]) -> str:
    return cast(
        str,
        sha256_hex(
            domain_sep_bytes("zenodex/fcis/m6/f06/external-evidence", version=1)
            + canonical_json_bytes(payload)
        ),
    )


def build_evidence(
    reopened: F03ReopenSuccessV1,
    *,
    external_authorization_root: str,
    activation_epoch: int = 0,
    expiration_epoch: int | None = 8,
) -> F06ExternalAuthorizationEvidenceV1:
    history = reopened.history
    payload: dict[str, object] = {
        "schema": FCIS_M6_F06_REOPEN_AUTHORIZATION_SCHEMA_V1,
        "snapshot_root": reopened.layout_root,
        "current_state_root": history.current_state_root,
        "authority_state_root": history.current_authority.authority_state_root,
        "authority_epoch": history.current_authority.epoch_index,
        "deployment_config_root": history.deployment_config_root,
        "external_authorization_root": external_authorization_root,
        "activation_epoch": activation_epoch,
        "expiration_epoch": expiration_epoch,
    }
    return F06ExternalAuthorizationEvidenceV1(
        snapshot_root=reopened.layout_root,
        current_state_root=history.current_state_root,
        authority_state_root=history.current_authority.authority_state_root,
        authority_epoch=history.current_authority.epoch_index,
        deployment_config_root=history.deployment_config_root,
        external_authorization_root=external_authorization_root,
        activation_epoch=activation_epoch,
        expiration_epoch=expiration_epoch,
        evidence_root=_evidence_root(payload),
    )


class AcceptingVerifier:
    """Test verifier that accepts only exact point-of-use subjects."""

    def __init__(self) -> None:
        self.calls = 0

    def verify_f06_reopen_authorization(
        self,
        evidence: object,
        *,
        expected_head_root: object,
        expected_snapshot_root: object,
        expected_current_state_root: object,
        expected_authority_state_root: object,
        expected_authority_epoch: object,
        expected_deployment_config_root: object,
        expected_external_authorization_root: object,
        current_epoch: object,
    ) -> object:
        self.calls += 1
        if type(evidence) is not F06ExternalAuthorizationEvidenceV1:
            return False
        checked = evidence
        return (
            checked.snapshot_root == expected_snapshot_root
            and checked.current_state_root == expected_current_state_root
            and checked.authority_state_root == expected_authority_state_root
            and checked.authority_epoch == expected_authority_epoch
            and checked.deployment_config_root == expected_deployment_config_root
            and checked.external_authorization_root == expected_external_authorization_root
            and type(expected_head_root) is str
            and type(current_epoch) is int
        )


class RejectingVerifier(AcceptingVerifier):
    def verify_f06_reopen_authorization(
        self,
        evidence: object,
        *,
        expected_head_root: object,
        expected_snapshot_root: object,
        expected_current_state_root: object,
        expected_authority_state_root: object,
        expected_authority_epoch: object,
        expected_deployment_config_root: object,
        expected_external_authorization_root: object,
        current_epoch: object,
    ) -> object:
        self.calls += 1
        return False


def _require_reject(value: object, code: F06AuthorizationCodeV1, message: str) -> None:
    if type(value) is not F06AuthorizationRejectV1:
        raise AssertionError(message)
    if value.code is not code:
        raise AssertionError(f"{message}: got {value.code.value}")


def run_checks(*, check_vector: bool = True) -> dict[str, object]:
    layout = build_layout()
    reopened = reopen_layout(layout)
    if type(reopened) is not F03ReopenSuccessV1:
        raise AssertionError("F03 fixture did not reopen")
    genesis = build_genesis(layout)
    external_root = _root("external-authorization")
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
    if type(issued) is not F06AuthorizationTokenV1:
        raise AssertionError("F06 rejected canonical reopen authorization")
    if verifier.calls != 1:
        raise AssertionError("F06 did not invoke the external verifier at issue")
    token = issued
    if token.evidence.evidence_root != derive_f06_evidence_root_v1(evidence):
        raise AssertionError("F06 evidence root is not stable")

    uses: dict[str, object] = {}
    for operation in F06OperationV1:
        use = require_f06_token_at_use(
            reopened,
            genesis=genesis,
            token=token,
            operation=operation,
            verifier_adapter=verifier,
            current_epoch=3,
        )
        if type(use) is not F06AuthorizationUseV1:
            raise AssertionError(f"F06 rejected {operation.value} token use")
        uses[operation.value] = use.token_root
    if verifier.calls != 4:
        raise AssertionError("F06 did not freshly verify every operation use")

    crossed = build_evidence(
        reopened,
        external_authorization_root=external_root,
    )
    object.__setattr__(crossed, "snapshot_root", _root("foreign-snapshot"))
    _require_reject(
        issue_f06_reopen_token(
            reopened,
            genesis=genesis,
            external_authorization_root=external_root,
            evidence=crossed,
            verifier_adapter=verifier,
            current_epoch=3,
        ),
        F06AuthorizationCodeV1.EVIDENCE_REJECTED,
        "F06 accepted forged evidence with a crossed snapshot",
    )

    forged_token = object.__new__(type(token))
    object.__setattr__(forged_token, "head", token.head)
    object.__setattr__(forged_token, "evidence", token.evidence)
    object.__setattr__(forged_token, "token_root", _root("forged-token"))
    _require_reject(
        require_f06_token_at_use(
            reopened,
            genesis=genesis,
            token=forged_token,
            operation=F06OperationV1.COMMIT,
            verifier_adapter=verifier,
            current_epoch=3,
        ),
        F06AuthorizationCodeV1.TOKEN_REJECTED,
        "F06 accepted a forged token root",
    )

    changed_history = replace(
        build_history(),
        genesis_state_root=_root("changed-head"),
        atoms=(),
        acks=(),
    )
    changed_layout = encode_history(changed_history)
    changed_reopened = reopen_layout(changed_layout)
    if type(changed_reopened) is not F03ReopenSuccessV1:
        raise AssertionError("F06 changed-head fixture did not reopen")
    changed_genesis = build_genesis(changed_layout)
    _require_reject(
        require_f06_token_at_use(
            changed_reopened,
            genesis=changed_genesis,
            token=token,
            operation=F06OperationV1.COMMIT,
            verifier_adapter=verifier,
            current_epoch=3,
        ),
        F06AuthorizationCodeV1.HEAD_MISMATCH,
        "F06 reused a token after the reopened head changed",
    )

    _require_reject(
        issue_f06_reopen_token(
            reopened,
            genesis=genesis,
            external_authorization_root=external_root,
            evidence=evidence,
            verifier_adapter=RejectingVerifier(),
            current_epoch=3,
        ),
        F06AuthorizationCodeV1.EXTERNAL_REJECTED,
        "F06 accepted a rejecting external verifier",
    )
    _require_reject(
        require_f06_token_at_use(
            reopened,
            genesis=genesis,
            token=token,
            operation=F06OperationV1.COMMIT,
            verifier_adapter=verifier,
            current_epoch=8,
        ),
        F06AuthorizationCodeV1.AUTHORIZATION_EXPIRED,
        "F06 accepted an expired token",
    )
    if check_vector:
        expected = json.loads(VECTOR_PATH.read_text(encoding="utf-8"))
        if canonical_json_bytes(build_payload()) != canonical_json_bytes(expected):
            raise SystemExit("FAIL: F06 reopen-authorization vector is stale")
    return build_payload()


def build_payload() -> dict[str, object]:
    layout = build_layout()
    reopened = reopen_layout(layout)
    if type(reopened) is not F03ReopenSuccessV1:
        raise AssertionError("F06 vector fixture did not reopen")
    genesis = build_genesis(layout)
    external_root = _root("external-authorization")
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
    if type(token) is not F06AuthorizationTokenV1:
        raise AssertionError("F06 vector token was rejected")
    return {
        "schema": FCIS_M6_F06_REOPEN_AUTHORIZATION_SCHEMA_V1,
        "genesis_root": token.head.genesis_root,
        "snapshot_root": token.head.snapshot_root,
        "current_state_root": token.head.current_state_root,
        "authority_state_root": token.head.authority_state_root,
        "authority_epoch": token.head.authority_epoch,
        "deployment_config_root": token.head.deployment_config_root,
        "external_authorization_root": token.head.external_authorization_root,
        "head_root": token.head.head_root,
        "evidence_root": token.evidence.evidence_root,
        "token_root": token.token_root,
        "operation_enum": [operation.value for operation in F06OperationV1],
        "fresh_verifier_calls": 4,
        "mutants_rejected": [
            "crossed evidence snapshot",
            "forged token root",
            "changed reopened head",
            "rejecting external verifier",
            "expired token",
        ],
        "all_rejections_typed": True,
    }


def main() -> None:
    result = run_checks()
    print("F06_REOPEN_AUTHORIZATION_CHECKS_PASS", result["token_root"])


if __name__ == "__main__":
    main()
