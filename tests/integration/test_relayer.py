from __future__ import annotations

import json

from src.agents.relayer import create_batch
from src.state.intents import Intent, IntentKind, SignedIntent


def test_create_batch_serializes_nested_owned_intent_fields_without_aliasing() -> None:
    """RIPR: relayer wire output must recursively detach exact owned fields."""

    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id="0x" + "5b" * 32,
        sender_pubkey="0x" + "5c" * 48,
        deadline=99,
        fields={
            "nonce": 1,
            "route": {
                "assets": ["A", "B"],
                "limits": {"amount_in": 7, "min_amount_out": 6},
            },
        },
    )
    signed = SignedIntent(intent=intent, signature="0x" + "00" * 96)

    batch = create_batch([signed], batch_ref="height:7")
    rendered = json.dumps(batch, sort_keys=True)
    route = batch["intents"][0]["route"]
    route["limits"]["amount_in"] = 99

    assert '"amount_in": 7' in rendered
    assert intent.get_field("route")["limits"]["amount_in"] == 7
    assert batch["batch_ref"] == "height:7"
