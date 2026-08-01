"""K02 unique publication capability tests."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from experiments.fcis_m6_k02_commit_port_check import run_checks
from src.core import fcis_m6_d08_combined_anf as d08
from src.core.fcis_durable_retraction import tagged_digest
from src.core.fcis_m6_k02_commit_port import (
    K02CommitResolutionV1,
    K02CommitTransitionV1,
    K02Error,
    K02PublicationRequestV1,
    K02RejectCodeV1,
    K02RejectV1,
    initial_port_state_v1,
    publish_v1,
    unique_commit_port_v1,
)

_ROOT = Path(__file__).resolve().parents[2]


def _anf() -> d08.D08CombinedANFAcceptV1:
    return d08.D08CombinedANFAcceptV1(
        anf_root="0x" + ("b" * 64),
        _construction_token=d08._D08_CONSTRUCTION_TOKEN_V1,
    )


def _request(head_root: str) -> K02PublicationRequestV1:
    return K02PublicationRequestV1(
        commit_id=tagged_digest("k02/test/commit"),
        expected_pre_state_root=head_root,
        post_state_root=tagged_digest("k02/test/post"),
        authority_epoch_root=tagged_digest("k02/test/authority"),
        effect_root=tagged_digest("k02/test/effect"),
        sequence=0,
        anf_accept=_anf(),
    )


def test_k02_checker_passes_all_capability_witnesses() -> None:
    run_checks()


def test_k02_success_and_retry_use_the_same_singleton_port() -> None:
    port = unique_commit_port_v1()
    assert port is unique_commit_port_v1()
    state = initial_port_state_v1(tagged_digest("k02/test/head"))
    request = _request(state.head_root)

    first = publish_v1(port, state, request)
    assert isinstance(first, K02CommitTransitionV1)
    assert first.resolution is K02CommitResolutionV1.NEWLY_COMMITTED
    retry = port.publish(first.state, request)
    assert isinstance(retry, K02CommitTransitionV1)
    assert retry.resolution is K02CommitResolutionV1.ALREADY_COMMITTED
    assert retry.state == first.state


def test_k02_wrong_capability_and_stale_head_fail_closed() -> None:
    state = initial_port_state_v1(tagged_digest("k02/test/head-2"))
    request = _request(state.head_root)
    wrong = publish_v1(object(), state, request)
    assert isinstance(wrong, K02RejectV1)
    assert wrong.code is K02RejectCodeV1.WRONG_CAPABILITY

    first = publish_v1(unique_commit_port_v1(), state, request)
    assert isinstance(first, K02CommitTransitionV1)
    stale_request = K02PublicationRequestV1(
        commit_id=tagged_digest("k02/test/stale"),
        expected_pre_state_root=state.head_root,
        post_state_root=tagged_digest("k02/test/stale-post"),
        authority_epoch_root=request.authority_epoch_root,
        effect_root=tagged_digest("k02/test/stale-effect"),
        sequence=1,
        anf_accept=_anf(),
    )
    stale = publish_v1(unique_commit_port_v1(), first.state, stale_request)
    assert isinstance(stale, K02RejectV1)
    assert stale.code is K02RejectCodeV1.STALE_HEAD
    assert first.state == stale_state(first.state, stale)


def test_k02_raw_anf_and_caller_minted_port_are_rejected() -> None:
    state = initial_port_state_v1(tagged_digest("k02/test/head-3"))
    with pytest.raises(K02Error, match="D08"):
        K02PublicationRequestV1(
            commit_id=tagged_digest("k02/test/raw"),
            expected_pre_state_root=state.head_root,
            post_state_root=tagged_digest("k02/test/raw-post"),
            authority_epoch_root=tagged_digest("k02/test/raw-authority"),
            effect_root=tagged_digest("k02/test/raw-effect"),
            sequence=0,
            anf_accept=object(),
        )
    with pytest.raises((K02Error, TypeError), match="controlled|unique"):
        from src.core.fcis_m6_k02_commit_port import K02CommitPortV1

        K02CommitPortV1(
            port_id="fcis/m6/unique-atomic-commit-port/v1",
            _construction_token=object(),
        )


def test_k02_dependency_rules_are_explicit_json() -> None:
    rules = json.loads(
        (_ROOT / "config/deploy/fcis_m6_k02_dependency_rules_v1.json").read_text(encoding="utf-8")
    )
    assert rules["unique_port_module"] == "src/core/fcis_m6_k02_commit_port.py"
    assert "sqlite3" in rules["forbidden_core_imports"]
    assert "direct_outbox_write" in rules["forbidden_core_effects"]


def stale_state(state: object, result: K02RejectV1) -> object:
    assert result.code is K02RejectCodeV1.STALE_HEAD
    return state
