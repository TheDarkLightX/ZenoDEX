"""Registered-empty lane producers (wave A) against the shared certificate fixture.

Obligation: for EXTERNAL_CUSTODY and PROOF_REWARDS the producer is a pure function of
the committed lane root that yields exactly the fragment the accepted registered-empty
certificate carries, rejects (producing nothing) when the lane is enabled, committed at
a foreign root, or not registered as empty, and the certificate checker refuses a
registered-empty lane committed away from its empty state root. The Rust test
``zk/global_settlement_abi_v1/tests/global_accounting_lane_producers.rs`` replays the
same fixture. Authority: NONE.
"""

from __future__ import annotations

import json
from dataclasses import replace
from pathlib import Path

import pytest

from src.core import global_accounting_allocation_certificate_v1 as cert
from src.core import global_accounting_lane_producers_v1 as producers
from src.core.external_custody_disabled_lane_v1 import ExternalCustodyDisabledStateV1
from src.core.global_settlement_types_v1 import LaneIdV1, canonical_global_bytes_v1
from src.core.proof_rewards_policy_blocked_lane_v1 import ProofRewardsPolicyBlockedStateV1
from tools import render_global_accounting_allocation_certificate_v1_golden as renderer

ROOT = Path(__file__).resolve().parents[2]
FIXTURE = ROOT / "tests/data/global_accounting_allocation_certificate_v1_golden.json"
ACCEPTED = "accepts_registered_empty_certificate_over_empty_state"


def test_registered_empty_roots_are_the_unique_empty_lane_states() -> None:
    assert cert.REGISTERED_EMPTY_LANE_ROOTS_V1 == {
        LaneIdV1.EXTERNAL_CUSTODY: ExternalCustodyDisabledStateV1().state_root,
        LaneIdV1.PROOF_REWARDS: ProofRewardsPolicyBlockedStateV1().state_root,
    }
    assert producers.REGISTERED_EMPTY_PRODUCER_LANES_V1 == (LaneIdV1.PROOF_REWARDS, LaneIdV1.EXTERNAL_CUSTODY)
    assert list(producers.LANE_PRODUCER_REJECT_MESSAGE_BY_CODE_V1) == list(producers.LaneProducerRejectCodeV1)


@pytest.mark.parametrize("lane", producers.REGISTERED_EMPTY_PRODUCER_LANES_V1, ids=lambda lane: lane.value)
def test_producer_reproduces_the_accepted_fixture_fragment(lane: LaneIdV1) -> None:
    fixture = json.loads(FIXTURE.read_text(encoding="utf-8"))
    vector = fixture["vectors"][ACCEPTED]
    state = renderer.build_state_v1(vector["spec"])
    lane_root = next(row for row in state.lane_roots if row.lane_id is lane)
    produced = producers.produce_registered_empty_fragment_v1(lane_root)
    assert isinstance(produced, cert.LaneAllocationFragmentV1)
    expected = next(f for f in vector["certificate"]["ordered_lane_fragments"] if f["lane_id"] == lane.value)
    assert json.loads(canonical_global_bytes_v1(produced)) == expected
    assert produced.is_empty and produced.enabled is False and produced.lane_state_root == cert.REGISTERED_EMPTY_LANE_ROOTS_V1[lane]


def test_producer_rejects_enabled_foreign_root_and_unregistered_lanes() -> None:
    state = renderer.build_state_v1(renderer._spec())
    lane_root = next(row for row in state.lane_roots if row.lane_id is LaneIdV1.EXTERNAL_CUSTODY)
    enabled = producers.produce_registered_empty_fragment_v1(replace(lane_root, enabled=True))
    assert isinstance(enabled, producers.LaneProducerRejectedV1) and enabled.code is producers.LaneProducerRejectCodeV1.LANE_ENABLED
    foreign = producers.produce_registered_empty_fragment_v1(replace(lane_root, state_root=renderer._root(4_242)))
    assert isinstance(foreign, producers.LaneProducerRejectedV1)
    assert foreign.code is producers.LaneProducerRejectCodeV1.REGISTERED_EMPTY_ROOT_DRIFT
    assert foreign.committed_lane_root == renderer._root(4_242) and foreign.lane_id is LaneIdV1.EXTERNAL_CUSTODY
    other = next(row for row in state.lane_roots if row.lane_id is LaneIdV1.ASSET_TRANSFER)
    unregistered = producers.produce_registered_empty_fragment_v1(other)
    assert isinstance(unregistered, producers.LaneProducerRejectedV1)
    assert unregistered.code is producers.LaneProducerRejectCodeV1.LANE_NOT_REGISTERED_EMPTY
    assert unregistered.to_canonical()["message"] == "lane has no registered-empty producer"
    with pytest.raises(TypeError):
        producers.produce_registered_empty_fragment_v1(object())  # type: ignore[arg-type]


def test_checker_refuses_a_registered_empty_lane_at_a_foreign_root() -> None:
    fixture = json.loads(FIXTURE.read_text(encoding="utf-8"))
    vector = fixture["vectors"]["rejects_registered_empty_lane_with_foreign_root"]
    assert vector["expected_outcome"]["code"] == "REGISTERED_EMPTY_ROOT_DRIFT"
    state = renderer.build_state_v1(vector["spec"])
    outcome = cert.check_global_accounting_allocation_certificate_v1(cert.build_registered_empty_certificate_v1(state), state)
    assert isinstance(outcome, cert.AllocationCertificateRejectedV1)
    assert outcome.code is cert.AllocationCertificateRejectCodeV1.REGISTERED_EMPTY_ROOT_DRIFT
    assert outcome.detail == "PROOF_REWARDS"
    assert outcome.pre_state_root == outcome.post_state_root == state.state_root
    accepted = renderer.build_state_v1(renderer._spec())
    assert isinstance(cert.check_global_accounting_allocation_certificate_v1(cert.build_registered_empty_certificate_v1(accepted), accepted), cert.AllocationCertificateAcceptedV1)
