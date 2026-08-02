"""Deterministic E04 classifier fixture and source-bound vector builder."""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Final, cast

_ROOT = Path(__file__).resolve().parents[1]
if str(_ROOT) not in sys.path:
    sys.path.insert(0, str(_ROOT))

import tools.build_fcis_m6_e02_nonce_nullifier as e02_builder  # noqa: E402
from src.core.fcis_m6_e01_request_identity import E01RequestIdentityV1  # noqa: E402
from src.core.fcis_m6_e03_unique_commit_port import (  # noqa: E402
    E03CommitIdentityV1,
    _mint_e03_commit_identity_v1,
)
from src.core.fcis_m6_e04_retry_classifier import (  # noqa: E402
    FCIS_M6_E04_SCHEMA_V1,
    E04AttemptV1,
    E04ClientKnowledgeV1,
    E04DurableOutcomeV1,
    E04Error,
    E04ReopenReceiptV1,
    E04StoredStateV1,
    _mint_e04_attempt_v1,
    _mint_e04_reopen_receipt_v1,
    _mint_e04_stored_commit_v1,
    _mint_e04_stored_state_v1,
)
from src.state.canonical import canonical_json_bytes  # noqa: E402
from tools.build_fcis_m6_e03_database_uniqueness import (  # noqa: E402
    build_candidate as build_e03_candidate,
)

DEFAULT_OUTPUT_PATH: Final = Path("docs/research/m6_tasks/TASK_E04_RETRY_CLASSIFIER_V1.json")
DEFAULT_CONFIG_PATH: Final = Path("config/deploy/fcis_m6_e04_retry_classifier_v1.json")
E04_CONFIG_SCHEMA_V1: Final = "zenodex/fcis/m6/e04/retry-classifier-config/v1"
GENESIS_STATE_ROOT_V1: Final = "5" * 64
POST_STATE_ROOT_V1: Final = "6" * 64
AUTHORITY_STATE_ROOT_V1: Final = "9" * 64
VERIFIER_PROFILE_ROOT_V1: Final = "8" * 64
OTHER_STATE_ROOT_V1: Final = "7" * 64
OTHER_WRITER_ROOT_V1: Final = "a" * 64
REOPEN_DATASTORE_PROFILE_ROOT_V1: Final = "b" * 64


def build_request_identity() -> E01RequestIdentityV1:
    """Reconstruct the verifier-owned identity from the pinned E02 fixture."""

    return e02_builder._identity_from_e01_payload(e02_builder.build_e01_payload())


def build_attempt(
    *,
    commit: E03CommitIdentityV1 | None = None,
    expected_pre_root: str = GENESIS_STATE_ROOT_V1,
    writer_profile_root: str = "2" * 64,
    authority_state_root: str = AUTHORITY_STATE_ROOT_V1,
    verifier_profile_root: str = VERIFIER_PROFILE_ROOT_V1,
) -> E04AttemptV1:
    selected_commit = build_e03_candidate() if commit is None else commit
    return _mint_e04_attempt_v1(
        request_identity=build_request_identity(),
        commit=selected_commit,
        expected_pre_root=expected_pre_root,
        writer_profile_root=writer_profile_root,
        authority_state_root=authority_state_root,
        verifier_profile_root=verifier_profile_root,
    )


def build_state(
    *,
    attempts: tuple[tuple[E04AttemptV1, str], ...] = (),
    genesis_state_root: str = GENESIS_STATE_ROOT_V1,
    current_state_root: str = GENESIS_STATE_ROOT_V1,
    authority_epoch_index: int = 3,
    authority_state_root: str = AUTHORITY_STATE_ROOT_V1,
    allowed_writer_roots: tuple[str, ...] = ("2" * 64,),
    verifier_profile_root: str = VERIFIER_PROFILE_ROOT_V1,
) -> E04StoredStateV1:
    commits = tuple(
        _mint_e04_stored_commit_v1(attempt=attempt, post_state_root=post_root)
        for attempt, post_root in attempts
    )
    return _mint_e04_stored_state_v1(
        genesis_state_root=genesis_state_root,
        current_state_root=current_state_root,
        authority_epoch_index=authority_epoch_index,
        authority_state_root=authority_state_root,
        allowed_writer_roots=allowed_writer_roots,
        deployment_config_root=build_request_identity().deployment_config_root,
        verifier_profile_root=verifier_profile_root,
        commits=commits,
    )


def build_committed_state(attempt: E04AttemptV1 | None = None) -> E04StoredStateV1:
    selected_attempt = build_attempt() if attempt is None else attempt
    return build_state(
        attempts=((selected_attempt, POST_STATE_ROOT_V1),),
        current_state_root=POST_STATE_ROOT_V1,
    )


def build_reopen_receipt(
    state: E04StoredStateV1,
    *,
    read_version: int = 1,
    freshness_epoch: int = 1,
) -> E04ReopenReceiptV1:
    return _mint_e04_reopen_receipt_v1(
        state=state,
        datastore_profile_root=REOPEN_DATASTORE_PROFILE_ROOT_V1,
        read_version=read_version,
        freshness_epoch=freshness_epoch,
    )


def build_nullifier_collision_state() -> E04StoredStateV1:
    baseline = build_e03_candidate()
    other_commit = _mint_e03_commit_identity_v1(
        sequence=baseline.sequence,
        commit_id="f" * 64,
        nullifier=baseline.nullifier,
        effects=baseline.effects,
    )
    other_attempt = build_attempt(commit=other_commit)
    return build_state(
        attempts=((other_attempt, POST_STATE_ROOT_V1),), current_state_root=POST_STATE_ROOT_V1
    )


def build_payload() -> dict[str, object]:
    config = _load_config(_ROOT / DEFAULT_CONFIG_PATH)
    attempt = build_attempt()
    empty = build_state()
    committed = build_committed_state(attempt)
    empty_receipt = build_reopen_receipt(empty)
    committed_receipt = build_reopen_receipt(committed, freshness_epoch=2)
    if attempt.attempt_root != config["pinned_attempt_root"]:
        raise E04Error("E04 attempt root differs from its configured pin")
    if empty.snapshot_root != config["pinned_empty_snapshot_root"]:
        raise E04Error("E04 empty snapshot root differs from its configured pin")
    if committed.snapshot_root != config["pinned_committed_snapshot_root"]:
        raise E04Error("E04 committed snapshot root differs from its configured pin")
    outcomes = {
        "absent_confirmed": _classification_wire(
            attempt, empty, empty_receipt, E04ClientKnowledgeV1.CONFIRMED
        ),
        "absent_indeterminate": _classification_wire(
            attempt, empty, empty_receipt, E04ClientKnowledgeV1.INDETERMINATE
        ),
        "already_committed": _classification_wire(
            attempt, committed, committed_receipt, E04ClientKnowledgeV1.INDETERMINATE
        ),
    }
    return {
        "schema": FCIS_M6_E04_SCHEMA_V1,
        "config_schema": E04_CONFIG_SCHEMA_V1,
        "attempt": attempt.to_wire(),
        "empty_state": empty.to_wire(),
        "committed_state": committed.to_wire(),
        "empty_reopen_receipt": empty_receipt.to_wire(),
        "committed_reopen_receipt": committed_receipt.to_wire(),
        "outcomes": outcomes,
        "outcome_enum": [outcome.value for outcome in E04DurableOutcomeV1],
        "client_knowledge_enum": [knowledge.value for knowledge in E04ClientKnowledgeV1],
        "profile_id": config["profile_id"],
        "identifier_registry_version": config["identifier_registry_version"],
        "semantic_allocator_profile_id": config["semantic_allocator_profile_id"],
        "nonclaims": cast(list[str], config["nonclaims"]),
    }


def _load_config(path: Path) -> dict[str, object]:
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise E04Error("E04 configuration cannot be loaded") from exc
    if type(raw) is not dict:
        raise E04Error("E04 configuration must be an exact object")
    expected = {
        "schema",
        "profile_id",
        "identifier_registry_version",
        "semantic_allocator_profile_id",
        "pinned_attempt_root",
        "pinned_empty_snapshot_root",
        "pinned_committed_snapshot_root",
        "nonclaims",
    }
    if set(raw) != expected or raw["schema"] != E04_CONFIG_SCHEMA_V1:
        raise E04Error("E04 configuration fields are not exact")
    for name in (
        "profile_id",
        "identifier_registry_version",
        "semantic_allocator_profile_id",
    ):
        if type(raw[name]) is not str or not raw[name]:
            raise E04Error(f"E04 configuration {name} is invalid")
    for name in (
        "pinned_attempt_root",
        "pinned_empty_snapshot_root",
        "pinned_committed_snapshot_root",
    ):
        value = raw[name]
        if (
            type(value) is not str
            or len(value) != 64
            or any(character not in "0123456789abcdef" for character in value)
        ):
            raise E04Error(f"E04 configuration {name} is not a digest")
    nonclaims = raw["nonclaims"]
    if (
        type(nonclaims) is not list
        or not nonclaims
        or any(type(item) is not str or not item for item in nonclaims)
    ):
        raise E04Error("E04 configuration nonclaims are invalid")
    return cast(dict[str, object], raw)


def _classification_wire(
    attempt: E04AttemptV1,
    state: E04StoredStateV1,
    reopen_receipt: E04ReopenReceiptV1,
    knowledge: E04ClientKnowledgeV1,
) -> dict[str, object]:
    from src.core.fcis_m6_e04_retry_classifier import classify_e04_retry

    result = classify_e04_retry(attempt, state, knowledge, reopen_receipt)
    if not hasattr(result, "to_wire"):
        raise E04Error("E04 vector fixture produced a rejection")
    return cast(dict[str, object], result.to_wire())


def write_or_check(output: Path = _ROOT / DEFAULT_OUTPUT_PATH, *, check: bool) -> None:
    encoded = canonical_json_bytes(build_payload()) + b"\n"
    if check:
        if output.read_bytes() != encoded:
            raise SystemExit("FAIL: E04 retry-classifier vector is stale")
    else:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_bytes(encoded)


def main(argv: list[str] | None = None) -> int:
    args = list(argv or sys.argv[1:])
    check = "--check" in args
    if any(argument not in {"--check"} for argument in args):
        raise SystemExit("usage: fcis_m6_e04_retry_classifier.py [--check]")
    write_or_check(check=check)
    print("E04_RETRY_CLASSIFIER_VECTOR_MATCH")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
