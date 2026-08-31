from __future__ import annotations

import json
from dataclasses import replace
from typing import cast

import pytest

from src.core.asset_origin_registry_codec_v2 import (
    decode_asset_origin_registration_command_v2,
    decode_asset_origin_registration_context_v2,
    decode_asset_origin_registry_state_v2,
)
from src.core.asset_origin_registry_types_v2 import AssetOriginRegistrationAcceptedV2
from src.core.asset_origin_registry_v2 import transition_asset_origin_registration_v2
from src.core.global_settlement_types_v2 import (
    ExternalOutboxEnqueueV2,
    GlobalEconomicEffectPlanV2,
    canonical_global_bytes_v2,
    hash_global_v2,
)
from tools.render_global_settlement_abi_v2_asset_origin_golden import FIXTURE_PATH_V2


def _mapping(value: object) -> dict[str, object]:
    return cast(dict[str, object], value)


def _accepted_registration() -> AssetOriginRegistrationAcceptedV2:
    fixture = _mapping(json.loads(FIXTURE_PATH_V2.read_text(encoding="utf-8")))
    vectors = _mapping(_mapping(fixture["accepted"])["vectors"])

    def vector_bytes(name: str) -> bytes:
        return canonical_global_bytes_v2(_mapping(vectors[name])["canonical"])

    result = transition_asset_origin_registration_v2(
        decode_asset_origin_registration_context_v2(vector_bytes("context")),
        decode_asset_origin_registry_state_v2(vector_bytes("pre_state")),
        decode_asset_origin_registration_command_v2(vector_bytes("command")),
    )
    assert isinstance(result, AssetOriginRegistrationAcceptedV2)
    return result


def _root(label: str) -> str:
    return hash_global_v2("asset-origin-external-effect-test-v2", {"label": label})


def test_accepted_registration_rejects_outbox_before_external_root_bindings() -> None:
    honest = _accepted_registration()
    honest_post_state = honest.post_state
    honest_effects = honest.effects
    honest_journal = honest.module_journal
    forged_effects = GlobalEconomicEffectPlanV2(
        rows=honest_effects.rows,
        asset_conservation=honest_effects.asset_conservation,
        fee_conservation=honest_effects.fee_conservation,
        lane_writes=honest_effects.lane_writes,
        occurrence_consumptions=honest_effects.occurrence_consumptions,
        external_outbox_enqueue=(
            ExternalOutboxEnqueueV2(
                effect_id=_root("effect"),
                destination_id="external:adapter",
                payload_hash=_root("payload"),
                adapter_profile_root=_root("adapter"),
            ),
        ),
    )
    forged_journal = replace(
        honest_journal,
        private_port_root=_root("private-port"),
    )

    with pytest.raises(
        ValueError,
        match="asset origin registration created an external outbox effect",
    ):
        AssetOriginRegistrationAcceptedV2(
            honest.post_state,
            forged_effects,
            forged_journal,
        )

    assert honest.post_state == honest_post_state
    assert honest.effects == honest_effects
    assert honest.effects.external_outbox_enqueue == ()
    assert honest.module_journal == honest_journal
