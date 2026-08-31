from __future__ import annotations

from dataclasses import FrozenInstanceError

import pytest

from src.state.intents import CreatePoolIntent, Intent, IntentKind, SignedIntent, SwapIntent


def _hex32(byte: str) -> str:
    return "0x" + byte * 64


def _pubkey(byte: str) -> str:
    return "0x" + byte * 96


def test_intent_defaults_fields_and_field_helpers() -> None:
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_hex32("1"),
        sender_pubkey=_pubkey("a"),
        deadline=123,
        fields=None,
    )
    assert intent.fields == {}
    assert intent.get_field("missing", 7) == 7
    updated = intent.with_field("amount_in", 42)
    assert intent.get_field("amount_in") is None
    assert updated.get_field("amount_in") == 42
    assert updated.without_field("amount_in") == intent


def test_intent_snapshot_rejects_mutation() -> None:
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_hex32("1"),
        sender_pubkey=_pubkey("a"),
        deadline=123,
        fields={},
    )
    with pytest.raises(FrozenInstanceError):
        intent.fields = None  # type: ignore[misc]
    with pytest.raises(AttributeError):
        intent.set_field("pool_id", _hex32("b"))  # type: ignore[attr-defined]
    assert intent.fields == {}


def test_intent_get_wire_field_detaches_nested_value() -> None:
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.CREATE_POOL,
        intent_id=_hex32("1"),
        sender_pubkey=_pubkey("a"),
        deadline=123,
        fields={"curve_params": {"p": 2, "route": ["a", "b"]}},
    )

    detached = intent.get_wire_field("curve_params")
    detached["p"] = 99
    detached["route"][0] = "mutated"

    assert intent.get_wire_field("curve_params") == {
        "p": 2,
        "route": ["a", "b"],
    }
    assert intent.get_wire_field("missing", {"default": True}) == {
        "default": True
    }


@pytest.mark.parametrize("module", ["", "OtherSwap"])
def test_intent_rejects_invalid_module(module: str) -> None:
    with pytest.raises(ValueError, match="Invalid module:"):
        Intent(
            module=module,
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_hex32("1"),
            sender_pubkey=_pubkey("a"),
            deadline=123,
            fields={},
        )


@pytest.mark.parametrize("intent_id", ["", "abcd", "0x1234", "0x" + "zz" * 32])
def test_intent_rejects_invalid_intent_id(intent_id: str) -> None:
    with pytest.raises(ValueError, match="Invalid intent_id format:"):
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=intent_id,
            sender_pubkey=_pubkey("a"),
            deadline=123,
            fields={},
        )


def test_swap_intent_accepts_exact_in_and_exact_out() -> None:
    exact_in = SwapIntent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_hex32("1"),
        sender_pubkey=_pubkey("a"),
        deadline=123,
        fields={
            "pool_id": _hex32("b"),
            "asset_in": _hex32("c"),
            "asset_out": _hex32("d"),
            "amount_in": 10,
            "min_amount_out": 0,
        },
    )
    exact_out = SwapIntent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_OUT,
        intent_id=_hex32("2"),
        sender_pubkey=_pubkey("a"),
        deadline=123,
        fields={
            "pool_id": _hex32("b"),
            "asset_in": _hex32("c"),
            "asset_out": _hex32("d"),
            "amount_out": 5,
            "max_amount_in": 11,
            "recipient": _pubkey("b"),
        },
    )
    assert exact_in.get_field("amount_in") == 10
    assert exact_out.get_field("recipient") == _pubkey("b")


def test_swap_intent_rejects_non_swap_kind() -> None:
    with pytest.raises(ValueError, match="Invalid kind for SwapIntent"):
        SwapIntent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.ADD_LIQUIDITY,
            intent_id=_hex32("1"),
            sender_pubkey=_pubkey("a"),
            deadline=123,
            fields={
                "pool_id": _hex32("b"),
                "asset_in": _hex32("c"),
                "asset_out": _hex32("d"),
                "amount_in": 10,
                "min_amount_out": 0,
            },
        )


@pytest.mark.parametrize(
    ("field_name", "fields", "message"),
    [
        ("pool_id", {"asset_in": _hex32("c"), "asset_out": _hex32("d"), "amount_in": 10, "min_amount_out": 0}, "Missing required field: pool_id"),
        ("asset_in", {"pool_id": _hex32("b"), "asset_out": _hex32("d"), "amount_in": 10, "min_amount_out": 0}, "Missing required field: asset_in"),
        ("asset_out", {"pool_id": _hex32("b"), "asset_in": _hex32("c"), "amount_in": 10, "min_amount_out": 0}, "Missing required field: asset_out"),
    ],
)
def test_swap_intent_rejects_missing_required_fields(
    field_name: str, fields: dict[str, object], message: str
) -> None:
    del field_name
    with pytest.raises(ValueError, match=message):
        SwapIntent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_hex32("1"),
            sender_pubkey=_pubkey("a"),
            deadline=123,
            fields=fields,
        )


@pytest.mark.parametrize("recipient", ["", 7, None])
def test_swap_intent_rejects_invalid_recipient(recipient: object) -> None:
    with pytest.raises(ValueError, match="recipient must be a non-empty string"):
        SwapIntent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_hex32("1"),
            sender_pubkey=_pubkey("a"),
            deadline=123,
            fields={
                "pool_id": _hex32("b"),
                "asset_in": _hex32("c"),
                "asset_out": _hex32("d"),
                "amount_in": 10,
                "min_amount_out": 0,
                "recipient": recipient,
            },
        )


@pytest.mark.parametrize("amount_in", [None, 0, -1])
def test_swap_intent_rejects_invalid_exact_in_amount(amount_in: object) -> None:
    with pytest.raises(ValueError, match="amount_in must be positive"):
        SwapIntent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_hex32("1"),
            sender_pubkey=_pubkey("a"),
            deadline=123,
            fields={
                "pool_id": _hex32("b"),
                "asset_in": _hex32("c"),
                "asset_out": _hex32("d"),
                "amount_in": amount_in,
                "min_amount_out": 0,
            },
        )


@pytest.mark.parametrize("min_amount_out", [None, -1])
def test_swap_intent_rejects_invalid_exact_in_min_amount_out(min_amount_out: object) -> None:
    with pytest.raises(ValueError, match="min_amount_out must be non-negative"):
        SwapIntent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_hex32("1"),
            sender_pubkey=_pubkey("a"),
            deadline=123,
            fields={
                "pool_id": _hex32("b"),
                "asset_in": _hex32("c"),
                "asset_out": _hex32("d"),
                "amount_in": 1,
                "min_amount_out": min_amount_out,
            },
        )


@pytest.mark.parametrize("amount_out", [None, 0, -1])
def test_swap_intent_rejects_invalid_exact_out_amount(amount_out: object) -> None:
    with pytest.raises(ValueError, match="amount_out must be positive"):
        SwapIntent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_OUT,
            intent_id=_hex32("1"),
            sender_pubkey=_pubkey("a"),
            deadline=123,
            fields={
                "pool_id": _hex32("b"),
                "asset_in": _hex32("c"),
                "asset_out": _hex32("d"),
                "amount_out": amount_out,
                "max_amount_in": 1,
            },
        )


@pytest.mark.parametrize("max_amount_in", [None, -1])
def test_swap_intent_rejects_invalid_exact_out_max_amount_in(max_amount_in: object) -> None:
    with pytest.raises(ValueError, match="max_amount_in must be non-negative"):
        SwapIntent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_OUT,
            intent_id=_hex32("1"),
            sender_pubkey=_pubkey("a"),
            deadline=123,
            fields={
                "pool_id": _hex32("b"),
                "asset_in": _hex32("c"),
                "asset_out": _hex32("d"),
                "amount_out": 1,
                "max_amount_in": max_amount_in,
            },
        )


def test_create_pool_intent_accepts_valid_payload() -> None:
    intent = CreatePoolIntent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.CREATE_POOL,
        intent_id=_hex32("1"),
        sender_pubkey=_pubkey("a"),
        deadline=123,
        fields={
            "asset0": _hex32("0"),
            "asset1": _hex32("f"),
            "fee_bps": 30,
            "amount0": 10,
            "amount1": 20,
        },
    )
    assert intent.get_field("fee_bps") == 30


def test_create_pool_intent_rejects_wrong_kind() -> None:
    with pytest.raises(ValueError, match="Invalid kind for CreatePoolIntent"):
        CreatePoolIntent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_hex32("1"),
            sender_pubkey=_pubkey("a"),
            deadline=123,
            fields={
                "asset0": _hex32("0"),
                "asset1": _hex32("f"),
                "fee_bps": 30,
                "amount0": 10,
                "amount1": 20,
            },
        )


@pytest.mark.parametrize(
    "fields",
    [
        {"asset1": _hex32("f"), "fee_bps": 30, "amount0": 10, "amount1": 20},
        {"asset0": _hex32("0"), "fee_bps": 30, "amount0": 10, "amount1": 20},
    ],
)
def test_create_pool_intent_rejects_missing_assets(fields: dict[str, object]) -> None:
    with pytest.raises(ValueError, match="Missing required fields: asset0, asset1"):
        CreatePoolIntent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.CREATE_POOL,
            intent_id=_hex32("1"),
            sender_pubkey=_pubkey("a"),
            deadline=123,
            fields=fields,
        )


def test_create_pool_intent_rejects_non_canonical_assets() -> None:
    with pytest.raises(ValueError, match="Assets must be in canonical order"):
        CreatePoolIntent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.CREATE_POOL,
            intent_id=_hex32("1"),
            sender_pubkey=_pubkey("a"),
            deadline=123,
            fields={
                "asset0": _hex32("f"),
                "asset1": _hex32("0"),
                "fee_bps": 30,
                "amount0": 10,
                "amount1": 20,
            },
        )


@pytest.mark.parametrize("fee_bps", [None, -1, 10001])
def test_create_pool_intent_rejects_fee_bounds(fee_bps: object) -> None:
    with pytest.raises(ValueError, match="fee_bps must be in \\[0, 10000\\]"):
        CreatePoolIntent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.CREATE_POOL,
            intent_id=_hex32("1"),
            sender_pubkey=_pubkey("a"),
            deadline=123,
            fields={
                "asset0": _hex32("0"),
                "asset1": _hex32("f"),
                "fee_bps": fee_bps,
                "amount0": 10,
                "amount1": 20,
            },
        )


@pytest.mark.parametrize("field_name", ["amount0", "amount1"])
@pytest.mark.parametrize("amount", [None, 0, -1])
def test_create_pool_intent_rejects_non_positive_amounts(field_name: str, amount: object) -> None:
    fields: dict[str, object] = {
        "asset0": _hex32("0"),
        "asset1": _hex32("f"),
        "fee_bps": 30,
        "amount0": 10,
        "amount1": 20,
    }
    fields[field_name] = amount
    with pytest.raises(ValueError, match=rf"{field_name} must be positive"):
        CreatePoolIntent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.CREATE_POOL,
            intent_id=_hex32("1"),
            sender_pubkey=_pubkey("a"),
            deadline=123,
            fields=fields,
        )


def test_signed_intent_accepts_valid_signature() -> None:
    signed = SignedIntent(
        intent=Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_hex32("1"),
            sender_pubkey=_pubkey("a"),
            deadline=123,
            fields={},
        ),
        signature="0x" + "a" * 192,
    )
    assert signed.signature.startswith("0x")


@pytest.mark.parametrize("signature", ["", "abcd", "0x1234"])
def test_signed_intent_rejects_invalid_signature(signature: str) -> None:
    with pytest.raises(ValueError, match="Invalid signature format:"):
        SignedIntent(
            intent=Intent(
                module="TauSwap",
                version="0.1",
                kind=IntentKind.SWAP_EXACT_IN,
                intent_id=_hex32("1"),
                sender_pubkey=_pubkey("a"),
                deadline=123,
                fields={},
            ),
            signature=signature,
        )
