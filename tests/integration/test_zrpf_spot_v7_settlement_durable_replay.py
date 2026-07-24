"""CBC tests for durable, authority-neutral Spot V7 settlement replay."""

from __future__ import annotations

import copy
import json
import pickle
from dataclasses import replace
from typing import Any, cast

import pytest

import src.integration._zrpf_spot_v7_settlement_envelope_replay as replay_module
import src.integration._zrpf_spot_v7_settlement_replay_packet as packet_module
from src.integration._zrpf_spot_v7_settlement_durable_replay import (
    SpotV7SettlementDurableReplayErrorV2,
    _DurablyReverifiedSpotV7SettlementReplayV2,
    _require_durably_reverified_spot_v7_settlement_replay_v2,
    _reverify_persisted_spot_v7_settlement_replay_v2,
)
from src.integration._zrpf_spot_v7_settlement_envelope_contract import (
    _AuthenticatedSpotV7SettlementReplayObservationV2,
)
from src.integration._zrpf_spot_v7_settlement_envelope_replay import (
    SpotV7SettlementEnvelopeReplayAdapterV2,
)
from src.integration._zrpf_spot_v7_settlement_replay_packet import (
    _DurableSpotV7SettlementReplayPacketV2,
    _UntrustedPersistedSpotV7SettlementReplayInputsV2,
)
from src.integration.dex_engine import DexEngineConfig
from src.integration.zeno_ledger_replay import replay_engine_config_document_v0
from src.integration.zeno_ledger_v0 import (
    canonical_header_hash_v0,
    canonical_json_bytes_v0,
)
from tests.integration.test_zrpf_spot_v7_settlement_envelope_replay import (
    _Fixture,
    _fixture,
    _root,
    _settlement,
    _v2_observation,
)


def _packet_fixture() -> tuple[
    _Fixture,
    _AuthenticatedSpotV7SettlementReplayObservationV2,
    _DurableSpotV7SettlementReplayPacketV2,
    _UntrustedPersistedSpotV7SettlementReplayInputsV2,
]:
    fixture, observation = _v2_observation()
    packet = observation._durable_replay_packet_for_history_reverification()
    persisted = packet._persisted_inputs_for_storage()
    return fixture, observation, packet, persisted


def test_observation_exposes_all_exact_surfaces_only_through_sealed_packet() -> None:
    fixture, observation, packet, persisted = _packet_fixture()

    assert type(packet) is packet_module._DurableSpotV7SettlementReplayPacketV2
    assert type(persisted) is packet_module._UntrustedPersistedSpotV7SettlementReplayInputsV2
    assert json.loads(persisted.exact_projection_bytes) == (
        observation._canonical_projection_for_finality_adapter()
    )
    assert persisted.exact_header_bytes == canonical_json_bytes_v0(fixture.header)
    assert persisted.exact_body_bytes == canonical_json_bytes_v0(fixture.body)
    assert persisted.exact_envelope_bytes == canonical_json_bytes_v0(fixture.envelope)
    assert persisted.exact_receipt_bytes == canonical_json_bytes_v0(
        fixture.envelope["expected_receipt"]
    )
    assert persisted.exact_config_document_bytes
    assert persisted.exact_pre_state_snapshot_bytes == canonical_json_bytes_v0(fixture.pre_snapshot)
    assert persisted.exact_evidence_bytes
    assert not hasattr(observation, "_exact_header_bytes")
    assert not hasattr(observation, "_exact_body_bytes")
    assert not hasattr(observation, "_exact_envelope_bytes")
    assert not hasattr(observation, "_exact_receipt_bytes")
    assert not hasattr(observation, "_exact_evidence_bytes")
    assert not hasattr(observation, "_exact_config_document_bytes")
    assert not hasattr(observation, "_exact_pre_state_snapshot_bytes")
    assert packet.settlement_authority is False
    assert packet.release_authority is False
    assert packet.production_authority is False


def test_durable_packet_rejects_copy_pickle_mutation_and_forgery() -> None:
    _fixture, _observation, packet, _persisted = _packet_fixture()

    with pytest.raises(TypeError):
        copy.copy(packet)
    with pytest.raises(TypeError):
        copy.deepcopy(packet)
    with pytest.raises(TypeError):
        pickle.dumps(packet)
    with pytest.raises(TypeError):
        cast(Any, packet)._inputs = packet._persisted_inputs_for_storage()

    forged = object.__new__(packet_module._DurableSpotV7SettlementReplayPacketV2)
    with pytest.raises(TypeError):
        packet_module._require_durable_spot_v7_settlement_replay_packet_v2(forged)


def test_persisted_exact_bytes_are_replayed_into_separate_authority_neutral_result() -> None:
    fixture, observation, _packet, persisted = _packet_fixture()

    result = _reverify_persisted_spot_v7_settlement_replay_v2(
        settlement=fixture.settlement,
        persisted=persisted,
    )
    replayed_packet = result._durable_replay_packet_for_history_commit()

    assert replayed_packet._persisted_inputs_for_storage() == persisted
    assert observation.durable_settlement_replay_reverified is False
    assert result.exact_replay_material_authenticated is True
    assert result.durable_settlement_replay_reverification_material_retained is True
    assert result.durable_settlement_replay_reverified is True
    assert result.proof_receipt_authentication_established is False
    assert result.application_domain_to_ledger_chain_binding_established is False
    assert result.settlement_authority is False
    assert result.release_authority is False
    assert result.production_authority is False


def test_durable_reverification_executes_the_exact_replay_once(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture, _observation, _packet, persisted = _packet_fixture()
    original = replay_module._evaluate
    calls = 0

    def counted(*args: Any, **kwargs: Any) -> Any:
        nonlocal calls
        calls += 1
        return original(*args, **kwargs)

    monkeypatch.setattr(replay_module, "_evaluate", counted)

    result = _reverify_persisted_spot_v7_settlement_replay_v2(
        settlement=fixture.settlement,
        persisted=persisted,
    )

    assert calls == 1
    assert result.durable_settlement_replay_reverified is True


def test_durable_reverification_result_rejects_copy_pickle_mutation_and_forgery() -> None:
    fixture, _observation, _packet, persisted = _packet_fixture()
    result = _reverify_persisted_spot_v7_settlement_replay_v2(
        settlement=fixture.settlement,
        persisted=persisted,
    )

    with pytest.raises(TypeError):
        copy.copy(result)
    with pytest.raises(TypeError):
        copy.deepcopy(result)
    with pytest.raises(TypeError):
        pickle.dumps(result)
    with pytest.raises(TypeError):
        cast(Any, result)._packet = result._durable_replay_packet_for_history_commit()

    forged = object.__new__(_DurablyReverifiedSpotV7SettlementReplayV2)
    with pytest.raises(TypeError):
        _require_durably_reverified_spot_v7_settlement_replay_v2(forged)
    with pytest.raises(TypeError):
        _ = forged.durable_settlement_replay_reverified


def _mutate_exact_json_surface(persisted: Any, surface: str) -> Any:
    field_name = f"exact_{surface}_bytes"
    document = json.loads(getattr(persisted, field_name))
    if surface == "header":
        document["time_ms"] += 1
    elif surface == "body":
        document["height"] += 1
    elif surface == "envelope":
        document["proposal"]["economic_action_id"] = _root("mutated-envelope-action")
    elif surface == "receipt":
        document["economic_action_id"] = _root("mutated-receipt-action")
    elif surface == "evidence":
        document["status"] = "mutated-persisted-evidence"
    elif surface == "config_document":
        document["config"]["max_intents"] += 1
    elif surface == "pre_state_snapshot":
        document["balances"][0]["amount"] += 1
    else:  # pragma: no cover - the parametrization is the closed inventory.
        raise AssertionError(f"unknown exact replay surface: {surface}")
    return replace(persisted, **{field_name: canonical_json_bytes_v0(document)})


@pytest.mark.parametrize(
    "surface",
    (
        "header",
        "body",
        "envelope",
        "receipt",
        "evidence",
        "config_document",
        "pre_state_snapshot",
    ),
)
def test_each_persisted_exact_byte_surface_mutation_rejects(surface: str) -> None:
    fixture, _observation, _packet, persisted = _packet_fixture()
    mutated = _mutate_exact_json_surface(persisted, surface)

    with pytest.raises(SpotV7SettlementDurableReplayErrorV2) as captured:
        _reverify_persisted_spot_v7_settlement_replay_v2(
            settlement=fixture.settlement,
            persisted=mutated,
        )

    assert captured.value.code == "persisted_packet_binding"


def test_persisted_projection_mutation_rejects() -> None:
    fixture, _observation, _packet, persisted = _packet_fixture()
    projection = json.loads(persisted.exact_projection_bytes)
    projection["height"] += 1
    mutated = replace(
        persisted,
        exact_projection_bytes=canonical_json_bytes_v0(projection),
    )

    with pytest.raises(SpotV7SettlementDurableReplayErrorV2) as captured:
        _reverify_persisted_spot_v7_settlement_replay_v2(
            settlement=fixture.settlement,
            persisted=mutated,
        )

    assert captured.value.code == "persisted_packet_binding"


@pytest.mark.parametrize(
    "field_name",
    (
        "exact_projection_bytes",
        "exact_header_bytes",
        "exact_body_bytes",
        "exact_envelope_bytes",
        "exact_receipt_bytes",
        "exact_evidence_bytes",
        "exact_config_document_bytes",
        "exact_pre_state_snapshot_bytes",
    ),
)
def test_each_pathologically_nested_persisted_json_surface_rejects_with_stable_code(
    field_name: str,
) -> None:
    fixture, _observation, _packet, persisted = _packet_fixture()
    pathologically_nested = b"{" + (b'"x":{' * 10_000) + b'"x":0' + (b"}" * 10_001)
    mutated = replace(persisted, **{field_name: pathologically_nested})

    with pytest.raises(SpotV7SettlementDurableReplayErrorV2) as captured:
        _reverify_persisted_spot_v7_settlement_replay_v2(
            settlement=fixture.settlement,
            persisted=mutated,
        )

    assert captured.value.code == "persisted_packet_binding"


def test_persisted_replay_rejects_a_different_governed_candidate() -> None:
    fixture, _observation, _packet, persisted = _packet_fixture()
    different = replace(
        fixture.candidate,
        verified_program_id=_root("different-governed-program"),
    )

    with pytest.raises(SpotV7SettlementDurableReplayErrorV2) as captured:
        _reverify_persisted_spot_v7_settlement_replay_v2(
            settlement=_settlement(different),
            persisted=persisted,
        )

    assert captured.value.code == "exact_replay_rejected"


def test_persisted_replay_rejects_untyped_input() -> None:
    fixture, _observation, _packet, persisted = _packet_fixture()

    with pytest.raises(TypeError):
        _reverify_persisted_spot_v7_settlement_replay_v2(
            settlement=fixture.settlement,
            persisted={
                "exact_projection_bytes": persisted.exact_projection_bytes,
            },
        )


def test_persisted_replay_requires_private_settlement_capability() -> None:
    fixture, _observation, _packet, persisted = _packet_fixture()

    with pytest.raises(TypeError, match="settlement"):
        _reverify_persisted_spot_v7_settlement_replay_v2(
            settlement=fixture.candidate,
            persisted=persisted,
        )


def test_non_genesis_reverification_requires_and_checks_exact_parent_header() -> None:
    fixture = _fixture()
    parent = {
        **fixture.header,
        "height": 0,
        "post_state_root": fixture.candidate.pre_state_root,
    }
    child = {
        **fixture.header,
        "prev_header_hash": canonical_header_hash_v0(parent),
    }
    config = replay_engine_config_document_v0(DexEngineConfig(chain_id=child["chain_id"]))
    observation = SpotV7SettlementEnvelopeReplayAdapterV2(config).authenticate(
        settlement=fixture.settlement,
        header=child,
        body=fixture.body,
        pre_snapshot=fixture.pre_snapshot,
        parent_header=parent,
    )
    persisted = observation._durable_replay_packet_for_history_reverification()._persisted_inputs_for_storage()

    result = _reverify_persisted_spot_v7_settlement_replay_v2(
        settlement=fixture.settlement,
        persisted=persisted,
        exact_parent_header_bytes=canonical_json_bytes_v0(parent),
    )
    assert result.durable_settlement_replay_reverified is True

    with pytest.raises(SpotV7SettlementDurableReplayErrorV2) as captured:
        _reverify_persisted_spot_v7_settlement_replay_v2(
            settlement=fixture.settlement,
            persisted=persisted,
        )
    assert captured.value.code == "exact_replay_rejected"
