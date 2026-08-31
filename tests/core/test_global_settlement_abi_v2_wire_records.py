"""Adversarial evidence for the closed V2 wire-record boundary."""

from __future__ import annotations

import copy
import json
from dataclasses import replace
from typing import Callable, cast

import pytest

from src.core.global_economic_proof_v2 import EconomicCommandOccurrenceV2
from src.core.global_economic_refinement_outcome_v2 import (
    GlobalEconomicRefinementAcceptedV2,
    GlobalEconomicRefinementRejectCodeV2,
    GlobalEconomicRefinementRejectedV2,
    refine_global_economic_state_effects_outcome_v2,
)
from src.core.global_economic_state_effect_refinement_v2 import (
    GlobalEconomicStateEffectRefinementV2,
)
from src.core.global_economic_state_v2 import GlobalEconomicStateV2, LaneStateRootV2
from src.core.global_settlement_types_v2 import (
    ALL_LANE_IDS_V2,
    ZERO_ROOT_V2,
    AssetSupplyV2,
    EconomicAmountV2,
    ExternalOutboxEnqueueV2,
    GlobalEconomicEffectPlanV2,
    GlobalOracleOccurrencePlanV2,
    GlobalTerminalObligationPlanV2,
    LaneIdV2,
    canonical_global_bytes_v2,
)
from src.core.global_settlement_wire_codec_v2 import (
    MAX_GLOBAL_SETTLEMENT_WIRE_RECORD_CODEC_BYTES_V2,
    WIRE_RECORD_FIELD_SETS_V2,
    GlobalSettlementWireCodecErrorV2,
    _require_wire_record_codec_bytes_v2,
    decode_global_settlement_wire_record_v2,
    encode_global_settlement_wire_record_v2,
)
from src.core.global_settlement_wire_records_v2 import (
    WIRE_RECORD_TYPES_V2,
    AssetLaneAcceptedWireV2,
    AssetLaneContextWireV2,
    GlobalEconomicStateEffectRefinementCandidateWireV2,
)
from tools.render_global_settlement_abi_v2_wire_records_golden import (
    FIXTURE_PATH_V2,
    build_wire_records_v2,
    render_fixture_v2,
)


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _fixture() -> dict[str, object]:
    parsed = json.loads(FIXTURE_PATH_V2.read_text(encoding="utf-8"))
    assert type(parsed) is dict
    return parsed


def _encoded_fixture_records() -> dict[str, bytes]:
    records = _fixture()["records"]
    assert type(records) is dict
    encoded: dict[str, bytes] = {}
    for name, payload in records.items():
        assert type(name) is str
        assert type(payload) is dict
        canonical = payload["canonical"]
        assert type(canonical) is dict
        encoded[name] = canonical_global_bytes_v2(canonical)
    return encoded


def _mutated_record(
    name: str,
    mutate: Callable[[dict[str, object]], object],
) -> bytes:
    records = copy.deepcopy(_fixture()["records"])
    assert type(records) is dict
    payload = records[name]
    assert type(payload) is dict
    canonical = payload["canonical"]
    assert type(canonical) is dict
    mutate(canonical)
    return canonical_global_bytes_v2(canonical)


def _valid_oversized_candidate_wire_v2() -> GlobalEconomicStateEffectRefinementCandidateWireV2:
    balance_count = 10_000
    asset = "wire-codec-bound-asset"
    balances = tuple(
        EconomicAmountV2(f"owner-{index:05d}", asset, "accounts", 1)
        for index in range(balance_count)
    )
    state = GlobalEconomicStateV2(
        chain_id="wire-codec-bound-probe",
        deployment_root=_root(1_100),
        writer_epoch=1,
        height=1,
        profile_root=_root(1_101),
        lane_roots=tuple(
            LaneStateRootV2(
                lane,
                _root(1_200 + index),
                lane is not LaneIdV2.EXTERNAL_CUSTODY,
                _root(1_300 + index),
            )
            for index, lane in enumerate(ALL_LANE_IDS_V2)
        ),
        balances=balances,
        supplies=(AssetSupplyV2(asset, balance_count),),
        history_root=ZERO_ROOT_V2,
    )
    return GlobalEconomicStateEffectRefinementCandidateWireV2(
        state,
        state,
        GlobalEconomicEffectPlanV2.empty(),
        (),
        GlobalTerminalObligationPlanV2.empty(),
        GlobalOracleOccurrencePlanV2.empty(),
    )


def test_v2_wire_registry_has_exactly_eleven_closed_records() -> None:
    expected_names = tuple(record_type.__name__ for record_type in WIRE_RECORD_TYPES_V2)

    assert len(WIRE_RECORD_TYPES_V2) == 11
    assert tuple(WIRE_RECORD_FIELD_SETS_V2) == expected_names
    assert len(set(WIRE_RECORD_FIELD_SETS_V2.values())) == 11
    assert all("schema" not in fields for fields in WIRE_RECORD_FIELD_SETS_V2.values())


def test_wire_fixture_is_exactly_regenerated_and_round_trips_canonically() -> None:
    fixture = _fixture()
    assert fixture["authority"] == "NONE"
    assert fixture["profile_authentication"] == "SHADOW"
    assert FIXTURE_PATH_V2.read_text(encoding="utf-8") == render_fixture_v2()

    expected_types = tuple(record_type.__name__ for record_type in WIRE_RECORD_TYPES_V2)
    encoded_records = _encoded_fixture_records()
    assert frozenset(encoded_records) == frozenset(expected_types)
    for record_type in WIRE_RECORD_TYPES_V2:
        encoded = encoded_records[record_type.__name__]
        decoded = decode_global_settlement_wire_record_v2(encoded)

        assert type(decoded) is record_type
        assert encode_global_settlement_wire_record_v2(decoded) == encoded
        assert "schema" not in json.loads(encoded)


def test_only_context_and_candidate_records_can_become_domain_inputs() -> None:
    for record in build_wire_records_v2():
        decoded = decode_global_settlement_wire_record_v2(
            encode_global_settlement_wire_record_v2(record)
        )
        if isinstance(decoded, AssetLaneContextWireV2):
            assert decoded.to_domain_v2() is not None
        elif isinstance(decoded, GlobalEconomicStateEffectRefinementCandidateWireV2):
            assert decoded.to_domain_v2() is not None
        else:
            assert not hasattr(decoded, "to_domain_v2")


def test_context_and_candidate_wire_records_own_inputs_immutably() -> None:
    records = build_wire_records_v2()
    context = next(record for record in records if type(record) is AssetLaneContextWireV2)
    candidate = next(
        record
        for record in records
        if type(record) is GlobalEconomicStateEffectRefinementCandidateWireV2
    )
    context_before = encode_global_settlement_wire_record_v2(context)
    candidate_before = encode_global_settlement_wire_record_v2(candidate)

    context_input = context.to_domain_v2()
    candidate_input = candidate.to_domain_v2()
    object.__setattr__(context_input, "writer_epoch", 999)
    object.__setattr__(candidate_input, "_consumed_occurrences", ())

    assert encode_global_settlement_wire_record_v2(context) == context_before
    assert encode_global_settlement_wire_record_v2(candidate) == candidate_before


def test_candidate_wire_preserves_order_so_ordered_unique_rejection_remains_reachable() -> None:
    template = next(
        record
        for record in build_wire_records_v2()
        if type(record) is GlobalEconomicStateEffectRefinementCandidateWireV2
    )
    pre_state = template.pre_state
    first = EconomicCommandOccurrenceV2(
        chain_id=pre_state.chain_id,
        deployment_root=pre_state.deployment_root,
        height=pre_state.height + 1,
        tx_index=0,
        op_index=1,
        command_kind="wire-order-probe",
        command_body_hash=_root(801),
        route_release_id=_root(802),
        subject_id="alice",
        grant_root=_root(803),
        nonce=1,
        profile_root=pre_state.profile_root,
        pre_state_root=pre_state.state_root,
        consumed_object_ids=(),
    )
    second = replace(
        first,
        op_index=2,
        command_body_hash=_root(804),
        nonce=2,
    )
    ordered = tuple(sorted((first, second), key=lambda value: value.occurrence_id))
    effects = GlobalEconomicEffectPlanV2(
        (),
        (),
        (),
        (),
        tuple(value.occurrence_id for value in ordered),
        (),
    )
    wire_candidate = GlobalEconomicStateEffectRefinementCandidateWireV2(
        pre_state,
        replace(pre_state, height=pre_state.height + 1),
        effects,
        ordered[::-1],
        GlobalTerminalObligationPlanV2.empty(),
        GlobalOracleOccurrencePlanV2.empty(),
    )

    outcome = refine_global_economic_state_effects_outcome_v2(wire_candidate.to_domain_v2())

    assert wire_candidate.consumed_occurrences == ordered[::-1]
    assert type(outcome) is GlobalEconomicRefinementRejectedV2
    assert outcome.reject_code is (
        GlobalEconomicRefinementRejectCodeV2.OCCURRENCES_NOT_ORDERED_UNIQUE
    )
    assert outcome.pre_state_root == outcome.post_state_root
    assert outcome.effect_plan.is_empty


def test_asset_lane_accepted_outbox_mutant_rebinds_effect_root_then_rejects() -> None:
    raw = _encoded_fixture_records()["AssetLaneAcceptedWireV2"]
    decoded = decode_global_settlement_wire_record_v2(raw)
    assert type(decoded) is AssetLaneAcceptedWireV2
    outbox = ExternalOutboxEnqueueV2(
        _root(1_500),
        "remote-adapter",
        _root(1_501),
        _root(1_502),
    )
    effects = GlobalEconomicEffectPlanV2(
        decoded.effects.rows,
        decoded.effects.asset_conservation,
        decoded.effects.fee_conservation,
        decoded.effects.lane_writes,
        decoded.effects.occurrence_consumptions,
        (outbox,),
    )
    mutated = json.loads(canonical_global_bytes_v2(decoded.to_canonical()))
    assert type(mutated) is dict
    mutated["effects"] = json.loads(canonical_global_bytes_v2(effects.to_canonical()))
    journal = mutated["module_journal"]
    assert type(journal) is dict
    journal["effect_plan_root"] = effects.effect_plan_root
    rebound = canonical_global_bytes_v2(mutated)

    with pytest.raises(GlobalSettlementWireCodecErrorV2, match="external outbox"):
        decode_global_settlement_wire_record_v2(rebound)


@pytest.mark.parametrize(
    ("name", "mutate"),
    (
        (
            "GlobalEconomicRefinementAcceptedWireV2",
            lambda value: value.__setitem__("unknown", "value"),
        ),
        (
            "GlobalEconomicRefinementAcceptedWireV2",
            lambda value: value.pop("production_authority"),
        ),
        (
            "AssetOriginRegistrationRejectedWireV2",
            lambda value: value.__setitem__("code", "NOT_A_REJECT_CODE"),
        ),
        (
            "GlobalEconomicRefinementAcceptedWireV2",
            lambda value: value.__setitem__("production_authority", "SOME"),
        ),
        (
            "AssetLaneRejectedWireV2",
            lambda value: value.__setitem__("profile_authentication", "VERIFIED"),
        ),
        (
            "AssetLaneRejectedWireV2",
            lambda value: value.__setitem__("route", "MANAGED_LIFECYCLE"),
        ),
        (
            "GlobalEconomicStateEffectRefinementWireV2",
            lambda value: value.__setitem__("refinement_root", _root(997)),
        ),
        (
            "AssetOriginRegistrationRejectedWireV2",
            lambda value: value.__setitem__("post_state_root", _root(998)),
        ),
    ),
)
def test_closed_wire_mutants_fail_before_any_domain_witness(
    name: str,
    mutate: Callable[[dict[str, object]], object],
) -> None:
    raw = _mutated_record(name, mutate)

    with pytest.raises(GlobalSettlementWireCodecErrorV2):
        decode_global_settlement_wire_record_v2(raw)


def test_duplicate_noncanonical_and_float_wire_mutants_are_rejected() -> None:
    encoded = _encoded_fixture_records()["GlobalEconomicRefinementAcceptedWireV2"]
    noncanonical = json.dumps(json.loads(encoded), indent=2).encode("utf-8")

    for raw in (
        b'{"witness":{},"witness":{}}',
        noncanonical,
        b'{"production_authority":1.0}',
    ):
        with pytest.raises(GlobalSettlementWireCodecErrorV2):
            decode_global_settlement_wire_record_v2(raw)


def test_wire_transport_ceiling_rejects_oversized_input_without_refining_global_state() -> None:
    exact_bound = b"x" * MAX_GLOBAL_SETTLEMENT_WIRE_RECORD_CODEC_BYTES_V2
    oversized = b"x" * (MAX_GLOBAL_SETTLEMENT_WIRE_RECORD_CODEC_BYTES_V2 + 1)

    assert _require_wire_record_codec_bytes_v2(exact_bound) is exact_bound
    with pytest.raises(GlobalSettlementWireCodecErrorV2, match="codec byte bound"):
        _require_wire_record_codec_bytes_v2(oversized)
    with pytest.raises(GlobalSettlementWireCodecErrorV2, match="codec byte bound"):
        decode_global_settlement_wire_record_v2(oversized)


def test_valid_oversized_candidate_wire_is_rejected_at_encode_boundary() -> None:
    candidate = _valid_oversized_candidate_wire_v2()
    canonical = canonical_global_bytes_v2(candidate.to_canonical())

    assert len(candidate.pre_state.balances) == 10_000
    assert len(canonical) > MAX_GLOBAL_SETTLEMENT_WIRE_RECORD_CODEC_BYTES_V2
    with pytest.raises(GlobalSettlementWireCodecErrorV2, match="codec byte bound"):
        encode_global_settlement_wire_record_v2(candidate)


def test_fabricated_accepted_wire_data_cannot_construct_an_opaque_domain_witness() -> None:
    raw = _encoded_fixture_records()["GlobalEconomicRefinementAcceptedWireV2"]
    decoded = decode_global_settlement_wire_record_v2(raw)

    assert type(decoded).__name__ == "GlobalEconomicRefinementAcceptedWireV2"
    assert not hasattr(decoded, "to_domain_v2")
    with pytest.raises(TypeError, match="adapter-constructed"):
        GlobalEconomicRefinementAcceptedV2(
            object(),
            cast(GlobalEconomicStateEffectRefinementV2, object()),
        )
