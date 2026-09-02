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
from src.core.global_settlement_types_v1 import LaneIdV1, LaneStateRootV1, canonical_global_bytes_v1
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


# --- wave B: the receipt-backed ASSET_TRANSFER producer ---------------------


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _wave_b_accepted(custody=(), amount_atoms: int = 30):
    from src.core.asset_transfer_lane_module_v1 import (
        AssetTransferLaneModuleInputV1,
        transition_asset_transfer_lane_module_v1,
    )
    from src.core.asset_transfer_types_v1 import (
        ASSET_TRANSFER_COMMAND_KIND_V1,
        AssetTransferCommandV1,
        AssetTransferContextV1,
        AssetTransferPolicyV1,
        AssetTransferStateV1,
    )
    from src.core.global_settlement_types_v1 import AssetSupplyV1, EconomicAmountV1

    module_input = AssetTransferLaneModuleInputV1(
        context=AssetTransferContextV1(
            chain_id="zeno-asset-test",
            deployment_root=_root(1),
            profile_root=_root(2),
            writer_epoch=7,
            module_release_id=_root(3),
            command_occurrence_id=_root(4),
            subject_id="alice",
            grant_root=_root(5),
        ),
        pre_state=AssetTransferStateV1(
            module_release_id=_root(3),
            policies=(AssetTransferPolicyV1("USD", "treasury", 2, True),),
            balances=(
                EconomicAmountV1("alice", "USD", "accounts", 100),
                EconomicAmountV1("bob", "USD", "accounts", 10),
                EconomicAmountV1("treasury", "USD", "accounts", 5),
            ),
            supplies=(AssetSupplyV1("USD", 115 + sum(row.amount_atoms for row in custody)),),
        ),
        command=AssetTransferCommandV1(ASSET_TRANSFER_COMMAND_KIND_V1, "USD", "alice", "bob", amount_atoms, 2),
        asset_policy_registry_root=_root(11),
        fee_policy_registry_root=_root(12),
        custody=tuple(custody),
    )
    accepted = transition_asset_transfer_lane_module_v1(module_input)
    assert type(accepted).__name__ == "AssetTransferLaneModuleAcceptedV1", accepted
    return accepted


def _wave_b_setup():
    from src.core.global_settlement_types_v1 import EconomicAmountV1

    accepted = _wave_b_accepted(custody=(EconomicAmountV1("pool-a", "USD", "spot-pool", 5),))
    journal = accepted.module_journal
    lane_root = LaneStateRootV1(LaneIdV1.ASSET_TRANSFER, _root(3), True, journal.post_lane_root)
    prior = cert.LaneAllocationFragmentV1(
        lane_id=LaneIdV1.ASSET_TRANSFER,
        module_release_id=_root(3),
        enabled=True,
        lane_state_root=journal.pre_lane_root,
        producer_kind=cert.LaneProducerKindV1.RECEIPT_BACKED,
        binding_root=journal.pre_lane_root,
    )
    entitlements = (cert.ClaimantEntitlementRowV1("USD", "alice", "spot-pool", 5),)
    return accepted, lane_root, prior, entitlements


def test_receipt_backed_producer_accepts_and_binds_the_receipt_root() -> None:
    accepted, lane_root, prior, entitlements = _wave_b_setup()
    fragment = producers.produce_asset_transfer_fragment_v1(accepted, lane_root, prior, entitlements)
    assert isinstance(fragment, cert.LaneAllocationFragmentV1)
    assert fragment.lane_id is LaneIdV1.ASSET_TRANSFER and fragment.enabled is True
    assert fragment.producer_kind is cert.LaneProducerKindV1.RECEIPT_BACKED
    assert fragment.lane_state_root == accepted.module_journal.post_lane_root
    assert fragment.binding_root == accepted.module_journal.receipt_root
    assert fragment.controlled_locations == (cert.ControlledLocationRowV1("USD", "pool-a", "spot-pool", 5),)
    assert fragment.claimant_entitlements == entitlements
    assert fragment.unencumbered_reserves == () and fragment.pending_external_obligations == ()
    assert fragment.terminal_bindings == ()


@pytest.mark.parametrize(
    ("mutate", "expected_code", "expected_detail_fragment"),
    (
        pytest.param("foreign_lane", "JOURNAL_LANE_DRIFT", "committed SPOT_LIQUIDITY", id="journal_lane_drift"),
        pytest.param("disabled", "LANE_DISABLED", "lane disabled", id="lane_disabled"),
        pytest.param("release", "MODULE_RELEASE_DRIFT", "module release", id="module_release_drift"),
        pytest.param("post_root", "JOURNAL_ROOT_DRIFT", "post root", id="journal_root_drift"),
        pytest.param("stale_prior", "STALE_JOURNAL", "pre root", id="stale_journal"),
        pytest.param("coverage", "ENTITLEMENT_COVERAGE_DRIFT", "coverage", id="entitlement_coverage_drift"),
    ),
)
def test_receipt_backed_producer_rejects_each_binding_drift(
    mutate: str, expected_code: str, expected_detail_fragment: str
) -> None:
    from dataclasses import replace

    accepted, lane_root, prior, entitlements = _wave_b_setup()
    if mutate == "foreign_lane":
        lane_root = LaneStateRootV1(LaneIdV1.SPOT_LIQUIDITY, _root(3), True, lane_root.state_root)
    elif mutate == "disabled":
        lane_root = replace(lane_root, enabled=False)
    elif mutate == "release":
        lane_root = replace(lane_root, module_release_id=_root(99))
    elif mutate == "post_root":
        lane_root = replace(lane_root, state_root=_root(999))
    elif mutate == "stale_prior":
        prior = replace(prior, lane_state_root=_root(888), binding_root=_root(888))
    elif mutate == "coverage":
        entitlements = (cert.ClaimantEntitlementRowV1("USD", "alice", "spot-pool", 4),)
    outcome = producers.produce_asset_transfer_fragment_v1(accepted, lane_root, prior, entitlements)
    assert isinstance(outcome, producers.ReceiptBackedProducerRejectedV1)
    assert outcome.code.value == expected_code
    assert expected_detail_fragment in outcome.detail or outcome.detail == expected_detail_fragment
    assert outcome.lane_id is lane_root.lane_id
    assert outcome.committed_lane_root == lane_root.state_root
    assert outcome.message == producers.RECEIPT_BACKED_PRODUCER_REJECT_MESSAGE_BY_CODE_V1[outcome.code]


def test_receipt_backed_producer_rejects_entitlement_fold_overflow() -> None:
    """The controlled fold cannot overflow for well-formed inputs (supply conservation bounds
    custody totals at or below the u128 ceiling); the reachable overflow is the caller-provided
    entitlement rows, which no supply bounds."""

    accepted, lane_root, prior, _ = _wave_b_setup()
    max_atoms = cert.MAX_ATOMS_U128_V1
    entitlements = (
        cert.ClaimantEntitlementRowV1("USD", "alice", "spot-pool", max_atoms),
        cert.ClaimantEntitlementRowV1("USD", "bob", "spot-pool", max_atoms),
    )
    outcome = producers.produce_asset_transfer_fragment_v1(accepted, lane_root, prior, entitlements)
    assert isinstance(outcome, producers.ReceiptBackedProducerRejectedV1)
    assert outcome.code is producers.ReceiptBackedProducerRejectCodeV1.CONTROLLED_FOLD_OVERFLOW
    assert outcome.detail == "entitlements"


def test_receipt_backed_producer_reject_is_a_no_op_value() -> None:
    accepted, lane_root, prior, entitlements = _wave_b_setup()
    journal_before = canonical_global_bytes_v1(accepted.module_journal)
    port_root_before = accepted.private_port.port_root
    lane_root_before = canonical_global_bytes_v1(lane_root)
    prior_before = canonical_global_bytes_v1(prior)
    outcome = producers.produce_asset_transfer_fragment_v1(
        accepted, lane_root, prior, (cert.ClaimantEntitlementRowV1("USD", "alice", "spot-pool", 4),)
    )
    assert isinstance(outcome, producers.ReceiptBackedProducerRejectedV1)
    assert canonical_global_bytes_v1(accepted.module_journal) == journal_before
    assert accepted.private_port.port_root == port_root_before
    assert canonical_global_bytes_v1(lane_root) == lane_root_before
    assert canonical_global_bytes_v1(prior) == prior_before
    canonical = outcome.to_canonical()
    assert list(canonical) == ["code", "detail", "lane_id", "message", "committed_lane_root"]
