from __future__ import annotations

import pytest

from src.state.intents import (
    CreatePoolIntent,
    Intent,
    IntentKind,
    RouteIntent,
    SignedIntent,
    SwapIntent,
)


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
    intent.set_field("amount_in", 42)
    assert intent.get_field("amount_in") == 42


def test_intent_set_field_recovers_from_none_fields() -> None:
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_hex32("1"),
        sender_pubkey=_pubkey("a"),
        deadline=123,
        fields={},
    )
    intent.fields = None
    intent.set_field("pool_id", _hex32("b"))
    assert intent.fields == {"pool_id": _hex32("b")}


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
        signature="0x" + "a" * 130,
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


# ---------------------------------------------------------------------------
# RouteIntent — atomic route settlement intent model
# ---------------------------------------------------------------------------


def _route_exact_in_fields() -> dict[str, object]:
    return {
        "quote_receipt_hash": _hex32("e"),
        "asset_in": _hex32("c"),
        "asset_out": _hex32("d"),
        "leg_indices": [0, 1],
        "total_amount_in": 100,
        "total_min_amount_out": 90,
    }


def _route_exact_out_fields() -> dict[str, object]:
    return {
        "quote_receipt_hash": _hex32("e"),
        "asset_in": _hex32("c"),
        "asset_out": _hex32("d"),
        "leg_indices": [0, 1, 2],
        "total_amount_out": 100,
        "total_max_amount_in": 110,
    }


def _route(kind: IntentKind, fields: dict[str, object]) -> RouteIntent:
    return RouteIntent(
        module="TauSwap",
        version="0.1",
        kind=kind,
        intent_id=_hex32("1"),
        sender_pubkey=_pubkey("a"),
        deadline=123,
        fields=fields,
    )


def test_route_intent_accepts_valid_exact_in() -> None:
    intent = _route(IntentKind.ROUTE_EXACT_IN, _route_exact_in_fields())
    assert intent.get_field("leg_indices") == [0, 1]
    assert intent.get_field("total_amount_in") == 100
    assert intent.get_field("total_min_amount_out") == 90
    # Hash is canonicalized (lowercased, 0x-prefixed) back into the fields dict.
    assert intent.get_field("quote_receipt_hash") == _hex32("e")


def test_route_intent_accepts_valid_exact_out() -> None:
    intent = _route(IntentKind.ROUTE_EXACT_OUT, _route_exact_out_fields())
    assert intent.get_field("leg_indices") == [0, 1, 2]
    assert intent.get_field("total_amount_out") == 100
    assert intent.get_field("total_max_amount_in") == 110


def test_route_intent_canonicalizes_quote_receipt_hash() -> None:
    fields = _route_exact_in_fields()
    fields["quote_receipt_hash"] = "0x" + "E" * 64  # uppercase, should normalize
    intent = _route(IntentKind.ROUTE_EXACT_IN, fields)
    assert intent.get_field("quote_receipt_hash") == _hex32("e")


def test_route_intent_rejects_non_route_kind() -> None:
    with pytest.raises(ValueError, match="Invalid kind for RouteIntent"):
        _route(IntentKind.SWAP_EXACT_IN, _route_exact_in_fields())


@pytest.mark.parametrize(
    "quote_receipt_hash",
    [None, "", "abcd", "0x1234", "0x" + "zz" * 32],
)
def test_route_intent_rejects_invalid_quote_receipt_hash(
    quote_receipt_hash: object,
) -> None:
    fields = _route_exact_in_fields()
    fields["quote_receipt_hash"] = quote_receipt_hash
    with pytest.raises(ValueError, match="Invalid quote_receipt_hash format:"):
        _route(IntentKind.ROUTE_EXACT_IN, fields)


def test_route_intent_rejects_missing_quote_receipt_hash() -> None:
    fields = _route_exact_in_fields()
    del fields["quote_receipt_hash"]
    with pytest.raises(ValueError, match="Invalid quote_receipt_hash format:"):
        _route(IntentKind.ROUTE_EXACT_IN, fields)


@pytest.mark.parametrize("asset_in", [None, "", 7])
def test_route_intent_rejects_invalid_asset_in(asset_in: object) -> None:
    fields = _route_exact_in_fields()
    fields["asset_in"] = asset_in
    with pytest.raises(ValueError, match="asset_in must be a non-empty string"):
        _route(IntentKind.ROUTE_EXACT_IN, fields)


@pytest.mark.parametrize("asset_out", [None, "", 7])
def test_route_intent_rejects_invalid_asset_out(asset_out: object) -> None:
    fields = _route_exact_in_fields()
    fields["asset_out"] = asset_out
    with pytest.raises(ValueError, match="asset_out must be a non-empty string"):
        _route(IntentKind.ROUTE_EXACT_IN, fields)


def test_route_intent_rejects_same_in_out_asset() -> None:
    fields = _route_exact_in_fields()
    fields["asset_out"] = fields["asset_in"]
    with pytest.raises(ValueError, match="asset_in must differ from asset_out"):
        _route(IntentKind.ROUTE_EXACT_IN, fields)


@pytest.mark.parametrize("leg_indices", [None, [], "01", 0])
def test_route_intent_rejects_empty_or_non_list_leg_indices(
    leg_indices: object,
) -> None:
    fields = _route_exact_in_fields()
    fields["leg_indices"] = leg_indices
    with pytest.raises(ValueError, match="leg_indices must be a non-empty list"):
        _route(IntentKind.ROUTE_EXACT_IN, fields)


@pytest.mark.parametrize("leg_indices", [[-1, 0], [0, -1], [0, "1"], [0, True], [0, 1.0]])
def test_route_intent_rejects_negative_or_non_int_leg_index(
    leg_indices: object,
) -> None:
    fields = _route_exact_in_fields()
    fields["leg_indices"] = leg_indices
    with pytest.raises(ValueError, match="leg_indices must be non-negative ints"):
        _route(IntentKind.ROUTE_EXACT_IN, fields)


def test_route_intent_rejects_unsorted_leg_indices() -> None:
    fields = _route_exact_in_fields()
    fields["leg_indices"] = [1, 0]
    with pytest.raises(
        ValueError, match="leg_indices must be strictly ascending with no duplicates"
    ):
        _route(IntentKind.ROUTE_EXACT_IN, fields)


def test_route_intent_rejects_duplicate_leg_index() -> None:
    fields = _route_exact_in_fields()
    fields["leg_indices"] = [0, 1, 1, 2]
    with pytest.raises(
        ValueError, match="leg_indices must be strictly ascending with no duplicates"
    ):
        _route(IntentKind.ROUTE_EXACT_IN, fields)


@pytest.mark.parametrize("total_amount_in", [None, 0, -1, True, 1.0])
def test_route_intent_rejects_invalid_exact_in_total_amount_in(
    total_amount_in: object,
) -> None:
    fields = _route_exact_in_fields()
    fields["total_amount_in"] = total_amount_in
    with pytest.raises(ValueError, match="total_amount_in must be positive"):
        _route(IntentKind.ROUTE_EXACT_IN, fields)


@pytest.mark.parametrize("total_min_amount_out", [None, -1, True, 1.0])
def test_route_intent_rejects_invalid_exact_in_total_min_amount_out(
    total_min_amount_out: object,
) -> None:
    fields = _route_exact_in_fields()
    fields["total_min_amount_out"] = total_min_amount_out
    with pytest.raises(ValueError, match="total_min_amount_out must be non-negative"):
        _route(IntentKind.ROUTE_EXACT_IN, fields)


@pytest.mark.parametrize("total_amount_out", [None, 0, -1, True, 1.0])
def test_route_intent_rejects_invalid_exact_out_total_amount_out(
    total_amount_out: object,
) -> None:
    fields = _route_exact_out_fields()
    fields["total_amount_out"] = total_amount_out
    with pytest.raises(ValueError, match="total_amount_out must be positive"):
        _route(IntentKind.ROUTE_EXACT_OUT, fields)


@pytest.mark.parametrize("total_max_amount_in", [None, -1, True, 1.0])
def test_route_intent_rejects_invalid_exact_out_total_max_amount_in(
    total_max_amount_in: object,
) -> None:
    # None is the fail-closed case: max input MUST be specified (no default).
    fields = _route_exact_out_fields()
    fields["total_max_amount_in"] = total_max_amount_in
    with pytest.raises(ValueError, match="total_max_amount_in must be non-negative"):
        _route(IntentKind.ROUTE_EXACT_OUT, fields)


def test_route_intent_exact_out_requires_total_max_amount_in() -> None:
    # Absent (not just None) total_max_amount_in must fail closed.
    fields = _route_exact_out_fields()
    del fields["total_max_amount_in"]
    with pytest.raises(ValueError, match="total_max_amount_in must be non-negative"):
        _route(IntentKind.ROUTE_EXACT_OUT, fields)


@pytest.mark.parametrize("extra", ["total_amount_out", "total_max_amount_in"])
def test_route_intent_rejects_exact_out_fields_on_exact_in(extra: str) -> None:
    fields = _route_exact_in_fields()
    fields[extra] = 1
    with pytest.raises(ValueError, match="must not carry exact-out fields"):
        _route(IntentKind.ROUTE_EXACT_IN, fields)


@pytest.mark.parametrize("extra", ["total_amount_in", "total_min_amount_out"])
def test_route_intent_rejects_exact_in_fields_on_exact_out(extra: str) -> None:
    fields = _route_exact_out_fields()
    fields[extra] = 1
    with pytest.raises(ValueError, match="must not carry exact-in fields"):
        _route(IntentKind.ROUTE_EXACT_OUT, fields)


def test_existing_intents_unchanged_by_additive_route_kinds() -> None:
    """The additive ROUTE_* enum entries must not regress existing intents."""
    swap_in = SwapIntent(
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
    swap_out = SwapIntent(
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
        },
    )
    create_pool = CreatePoolIntent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.CREATE_POOL,
        intent_id=_hex32("3"),
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
    assert swap_in.get_field("amount_in") == 10
    assert swap_out.get_field("amount_out") == 5
    assert create_pool.get_field("fee_bps") == 30
    # Enum is purely additive: the original five kinds keep their values.
    assert IntentKind.SWAP_EXACT_IN.value == "SWAP_EXACT_IN"
    assert IntentKind.CREATE_POOL.value == "CREATE_POOL"
    assert IntentKind.ROUTE_EXACT_IN.value == "ROUTE_EXACT_IN"
    assert IntentKind.ROUTE_EXACT_OUT.value == "ROUTE_EXACT_OUT"
