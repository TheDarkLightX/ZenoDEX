"""K02 unique publication capability tests."""

from __future__ import annotations

import json
from functools import lru_cache
from pathlib import Path

import pytest

from experiments.fcis_m6_d08_combined_anf_check import build_instance
from experiments.fcis_m6_k02_commit_port_check import run_checks
from src.core import fcis_m6_d08_combined_anf as d08
from src.core.fcis_durable_retraction import PublicationAtomV1, tagged_digest
from src.core.fcis_m6_d08_combined_anf import verify_combined_anf_v1
from src.core.fcis_m6_k02_commit_port import (
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

_ROOT = Path(__file__).resolve().parents[2]


@lru_cache(maxsize=1)
def _anf() -> d08.D08CombinedANFAcceptV1:
    result = verify_combined_anf_v1(build_instance())
    if type(result) is not d08.D08CombinedANFAcceptV1:
        raise AssertionError(f"expected verified D08 fixture, got {result!r}")
    return result


def _request() -> K02PublicationRequestV1:
    return K02PublicationRequestV1(anf_accept=_anf())


def test_k02_checker_passes_all_capability_witnesses() -> None:
    run_checks()


def test_k02_success_and_retry_use_the_same_singleton_port() -> None:
    port = unique_commit_port_v1()
    assert port is unique_commit_port_v1()
    request = _request()
    state = initial_port_state_v1(request.expected_pre_state_root)

    first = publish_v1(port, state, request)
    assert isinstance(first, K02CommitTransitionV1)
    assert first.resolution is K02CommitResolutionV1.NEWLY_COMMITTED
    retry = port.publish(first.state, request)
    assert isinstance(retry, K02CommitTransitionV1)
    assert retry.resolution is K02CommitResolutionV1.ALREADY_COMMITTED
    assert retry.state == first.state


def test_k02_publish_replays_d08_exactly_once_per_attempt(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    request = _request()
    state = initial_port_state_v1(request.expected_pre_state_root)
    original = d08.authorized_publication_atom_v1
    calls = 0

    def counted(value: object) -> PublicationAtomV1:
        nonlocal calls
        calls += 1
        return original(value)

    monkeypatch.setattr(d08, "authorized_publication_atom_v1", counted)

    result = publish_v1(unique_commit_port_v1(), state, request)

    assert isinstance(result, K02CommitTransitionV1)
    assert calls == 1


def test_k02_wrong_capability_and_stale_head_fail_closed() -> None:
    request = _request()
    state = initial_port_state_v1(request.expected_pre_state_root)
    wrong = publish_v1(object(), state, request)
    assert isinstance(wrong, K02RejectV1)
    assert wrong.code is K02RejectCodeV1.WRONG_CAPABILITY

    stale = publish_v1(
        unique_commit_port_v1(),
        initial_port_state_v1(tagged_digest("k02/test/stale-head")),
        request,
    )
    assert isinstance(stale, K02RejectV1)
    assert stale.code is K02RejectCodeV1.STALE_HEAD

    first = publish_v1(unique_commit_port_v1(), state, request)
    assert isinstance(first, K02CommitTransitionV1)
    assert first.state != state


def test_k02_malformed_store_state_is_classified_as_wrong_state() -> None:
    request = _request()
    malformed = object.__new__(K02PortStateV1)
    object.__setattr__(malformed, "head_root", request.expected_pre_state_root)
    object.__setattr__(malformed, "next_sequence", 1)
    object.__setattr__(malformed, "records", (object(),))

    result = publish_v1(unique_commit_port_v1(), malformed, request)

    assert isinstance(result, K02RejectV1)
    assert result.code is K02RejectCodeV1.WRONG_STATE
    assert result.path == ("state",)


def test_k02_publication_fields_are_owned_by_d08_and_collision_is_state_bound() -> None:
    request = _request()
    collision_state = K02PortStateV1(
        head_root=request.expected_pre_state_root,
        next_sequence=2,
        records=(
            K02CommitRecordV1(
                sequence=1,
                commit_id=request.commit_id,
                fingerprint_root=tagged_digest("k02/test/foreign-fingerprint"),
                post_state_root=tagged_digest("k02/test/foreign-post"),
                response_root=tagged_digest("k02/test/foreign-response"),
            ),
        ),
    )
    collision = publish_v1(unique_commit_port_v1(), collision_state, request)
    assert isinstance(collision, K02RejectV1)
    assert collision.code is K02RejectCodeV1.COMMIT_COLLISION

    sequence_state = K02PortStateV1(
        head_root=request.expected_pre_state_root,
        next_sequence=2,
        records=(
            K02CommitRecordV1(
                sequence=1,
                commit_id=tagged_digest("k02/test/sequence-history"),
                fingerprint_root=tagged_digest("k02/test/sequence-fingerprint"),
                post_state_root=tagged_digest("k02/test/sequence-post"),
                response_root=tagged_digest("k02/test/sequence-response"),
            ),
        ),
    )
    sequence = publish_v1(unique_commit_port_v1(), sequence_state, request)
    assert isinstance(sequence, K02RejectV1)
    assert sequence.code is K02RejectCodeV1.SEQUENCE_MISMATCH


def test_k02_raw_anf_and_caller_minted_port_are_rejected() -> None:
    with pytest.raises(K02Error, match="D08"):
        K02PublicationRequestV1(anf_accept=object())
    forged = object.__new__(d08.D08CombinedANFAcceptV1)
    object.__setattr__(forged, "anf_root", _anf().anf_root)
    object.__setattr__(forged, "publication_atom", _anf().publication_atom)
    with pytest.raises(K02Error, match="D08"):
        K02PublicationRequestV1(anf_accept=forged)
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
