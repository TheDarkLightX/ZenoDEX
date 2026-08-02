"""Deterministic K02 unique commit-port checker and mutation witnesses."""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import cast

_ROOT = Path(__file__).resolve().parents[1]
if str(_ROOT) not in sys.path:
    sys.path.insert(0, str(_ROOT))

from experiments.fcis_m6_d08_combined_anf_check import build_instance  # noqa: E402
from src.core import fcis_m6_d08_combined_anf as d08  # noqa: E402
from src.core.fcis_durable_retraction import tagged_digest  # noqa: E402
from src.core.fcis_m6_d08_combined_anf import verify_combined_anf_v1  # noqa: E402
from src.core.fcis_m6_k02_commit_port import (  # noqa: E402
    K02CommitPortV1,
    K02CommitRecordV1,
    K02CommitResolutionV1,
    K02CommitTransitionV1,
    K02Error,
    K02PortStateV1,
    K02PublicationRequestV1,
    K02RejectCodeV1,
    K02RejectV1,
    initial_port_state_v1,
    publish_v1,
    unique_commit_port_v1,
)

_RULES = _ROOT / "config/deploy/fcis_m6_k02_dependency_rules_v1.json"


def _anf() -> d08.D08CombinedANFAcceptV1:
    result = verify_combined_anf_v1(build_instance())
    if type(result) is not d08.D08CombinedANFAcceptV1:
        raise AssertionError(f"expected verified D08 fixture, got {result!r}")
    return result


def _request() -> K02PublicationRequestV1:
    return K02PublicationRequestV1(anf_accept=_anf())


def _rules() -> dict[str, object]:
    value = json.loads(_RULES.read_text(encoding="utf-8"))
    if type(value) is not dict:
        raise AssertionError("K02 rules must be an object")
    return cast(dict[str, object], value)


def run_checks() -> None:
    rules = _rules()
    if rules["unique_port_id"] != "fcis/m6/unique-atomic-commit-port/v1":
        raise AssertionError("K02 unique port ID changed")
    forbidden = rules["forbidden_core_imports"]
    if type(forbidden) is not list or "sqlite3" not in forbidden or "socket" not in forbidden:
        raise AssertionError("K02 dependency rules do not forbid direct side-effect imports")

    port = unique_commit_port_v1()
    if port is not unique_commit_port_v1():
        raise AssertionError("K02 did not return one singleton port identity")
    request = _request()
    initial = initial_port_state_v1(request.expected_pre_state_root)
    committed = publish_v1(port, initial, request)
    if not isinstance(committed, K02CommitTransitionV1):
        raise AssertionError(f"expected first commit, got {committed!r}")
    if committed.resolution is not K02CommitResolutionV1.NEWLY_COMMITTED:
        raise AssertionError("first commit was not newly committed")
    if committed.state.next_sequence != 2:
        raise AssertionError("first commit did not advance sequence")

    retried = publish_v1(port, committed.state, request)
    if not isinstance(retried, K02CommitTransitionV1):
        raise AssertionError(f"expected same-commit retry, got {retried!r}")
    if retried.resolution is not K02CommitResolutionV1.ALREADY_COMMITTED:
        raise AssertionError("same fingerprint did not classify as already committed")
    if retried.state != committed.state:
        raise AssertionError("same-commit retry changed durable port state")

    collision_state = K02PortStateV1(
        head_root=request.expected_pre_state_root,
        next_sequence=2,
        records=(
            K02CommitRecordV1(
                sequence=1,
                commit_id=request.commit_id,
                fingerprint_root=tagged_digest("k02/foreign-fingerprint"),
                post_state_root=tagged_digest("k02/post/collision"),
                response_root=tagged_digest("k02/response/collision"),
            ),
        ),
    )
    collision = publish_v1(port, collision_state, request)
    if (
        not isinstance(collision, K02RejectV1)
        or collision.code is not K02RejectCodeV1.COMMIT_COLLISION
    ):
        raise AssertionError("same commit ID with changed fingerprint was accepted")

    stale_result = publish_v1(
        port,
        initial_port_state_v1(tagged_digest("k02/stale-head")),
        request,
    )
    if (
        not isinstance(stale_result, K02RejectV1)
        or stale_result.code is not K02RejectCodeV1.STALE_HEAD
    ):
        raise AssertionError("stale expected head was not rejected")

    sequence_state = K02PortStateV1(
        head_root=request.expected_pre_state_root,
        next_sequence=2,
        records=(
            K02CommitRecordV1(
                sequence=1,
                commit_id=tagged_digest("k02/sequence-history"),
                fingerprint_root=tagged_digest("k02/sequence-fingerprint"),
                post_state_root=tagged_digest("k02/sequence-post"),
                response_root=tagged_digest("k02/sequence-response"),
            ),
        ),
    )
    sequence_result = publish_v1(port, sequence_state, request)
    if not isinstance(sequence_result, K02RejectV1):
        raise AssertionError("wrong sequence was accepted")
    if sequence_result.code is not K02RejectCodeV1.SEQUENCE_MISMATCH:
        raise AssertionError("wrong sequence returned the wrong rejection")

    forged_port = object()
    wrong_capability = publish_v1(forged_port, initial, request)
    if not isinstance(wrong_capability, K02RejectV1):
        raise AssertionError("forged capability did not reject")
    if wrong_capability.code is not K02RejectCodeV1.WRONG_CAPABILITY:
        raise AssertionError("forged capability returned the wrong rejection")

    try:
        K02CommitPortV1(
            port_id="fcis/m6/unique-atomic-commit-port/v1", _construction_token=object()
        )
    except (K02Error, TypeError):
        pass
    else:
        raise AssertionError("caller-minted K02 capability was accepted")

    try:
        K02CommitPortV1(port_id="fcis/m6/unique-atomic-commit-port/v1")  # type: ignore[call-arg]
    except TypeError:
        pass
    else:
        raise AssertionError("K02 port could be constructed without its controlled token")

    try:
        K02PublicationRequestV1(anf_accept=object())
    except K02Error:
        pass
    else:
        raise AssertionError("raw caller object was accepted as an ANF witness")


if __name__ == "__main__":
    run_checks()
    print("K02_COMMIT_PORT_MATCH")
