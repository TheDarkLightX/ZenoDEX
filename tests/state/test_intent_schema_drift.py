from __future__ import annotations

import pytest

from src.core.dex_intent_auth_message import build_dex_intent_signing_dict_v1
from src.core.domain_limits import DEX_LP_AMOUNT_MAX, DEX_POOL_RESERVE_MAX
from src.state.canonical import canonical_json_bytes
from src.state.intent_field_registry import intent_allowed_field_names_v1
from src.state.intent_snapshots import (
    OwnedIntentV1,
    admit_intent_batch,
    canonical_owned_intent_bytes_v1,
    snapshot_intent,
)
from src.state.intents import (
    CreatePoolIntent,
    Intent,
    IntentKind,
    RouteIntent,
    SwapIntent,
    ValidatedIntent,
)
from src.state.snapshot_combinators import AdmitCode
from src.state.state_snapshots import StateAdmissionError

INTENT_ID = "0x" + "11" * 32
SENDER = "0x" + "22" * 48


def _intent(kind: IntentKind, fields: dict[str, object]) -> Intent:
    return Intent("TauSwap", "0.1", kind, INTENT_ID, SENDER, 9, None, fields)


ALL_KIND_FIELDS = (
    (
        IntentKind.CREATE_POOL,
        {"asset0": "A", "asset1": "B", "fee_bps": 0, "amount0": 1, "amount1": 1},
    ),
    (
        IntentKind.ADD_LIQUIDITY,
        {
            "pool_id": "pool",
            "amount0_desired": 1,
            "amount1_desired": 1,
            "amount0_min": 0,
            "amount1_min": 0,
        },
    ),
    (
        IntentKind.REMOVE_LIQUIDITY,
        {"pool_id": "pool", "lp_amount": 1, "amount0_min": 0, "amount1_min": 0},
    ),
    (
        IntentKind.SWAP_EXACT_IN,
        {"pool_id": "pool", "asset_in": "A", "asset_out": "B", "amount_in": 1, "min_amount_out": 0},
    ),
    (
        IntentKind.SWAP_EXACT_OUT,
        {"pool_id": "pool", "asset_in": "A", "asset_out": "B", "amount_out": 1, "max_amount_in": 1},
    ),
    (
        IntentKind.ROUTE_EXACT_IN,
        {
            "asset_in": "A",
            "asset_out": "B",
            "leg_indices": [0],
            "total_amount_in": 1,
            "total_min_amount_out": 0,
        },
    ),
    (
        IntentKind.ROUTE_EXACT_OUT,
        {
            "asset_in": "A",
            "asset_out": "B",
            "leg_indices": [0],
            "total_amount_out": 1,
            "total_max_amount_in": 1,
        },
    ),
)


@pytest.mark.parametrize(("kind", "fields"), ALL_KIND_FIELDS)
def test_fcis_t_478_007_every_intent_kind_uses_closed_schema(
    kind: IntentKind,
    fields: dict[str, object],
) -> None:
    source = _intent(kind, fields)

    owned = snapshot_intent(source)

    assert type(owned) is OwnedIntentV1
    assert canonical_owned_intent_bytes_v1(owned) == canonical_json_bytes(
        build_dex_intent_signing_dict_v1(source)
    )


def test_fcis_t_478_008_unknown_and_missing_kind_fields_reject() -> None:
    unknown = _intent(
        IntentKind.SWAP_EXACT_IN,
        {
            "pool_id": "pool",
            "asset_in": "A",
            "asset_out": "B",
            "amount_in": 1,
            "min_amount_out": 0,
            "extra": 1,
        },
    )
    with pytest.raises(StateAdmissionError) as unknown_reject:
        snapshot_intent(unknown)
    assert unknown_reject.value.code is AdmitCode.UNKNOWN_FIELD

    missing = _intent(
        IntentKind.SWAP_EXACT_IN,
        {"pool_id": "pool", "asset_in": "A", "asset_out": "B", "amount_in": 1},
    )
    with pytest.raises(StateAdmissionError) as missing_reject:
        snapshot_intent(missing)
    # Exact-keyed-map cardinality is checked before field-name selection.
    assert missing_reject.value.code is AdmitCode.ITEM_LIMIT


def test_fcis_t_478_007_liquidity_minimum_bounds_remain_kind_specific() -> None:
    add = _intent(
        IntentKind.ADD_LIQUIDITY,
        {
            "pool_id": "pool",
            "amount0_desired": 1,
            "amount1_desired": 1,
            "amount0_min": DEX_LP_AMOUNT_MAX + 1,
            "amount1_min": 0,
        },
    )
    with pytest.raises(StateAdmissionError) as add_reject:
        snapshot_intent(add)
    assert add_reject.value.code is AdmitCode.OUT_OF_RANGE

    remove = _intent(
        IntentKind.REMOVE_LIQUIDITY,
        {
            "pool_id": "pool",
            "lp_amount": 1,
            "amount0_min": DEX_POOL_RESERVE_MAX,
            "amount1_min": 0,
        },
    )
    assert type(snapshot_intent(remove)) is OwnedIntentV1


def test_fcis_t_478_009_subclasses_and_mappings_are_not_authority_sources() -> None:
    class IntentSubclass(Intent):
        pass

    source = _intent(
        IntentKind.SWAP_EXACT_IN,
        {"pool_id": "pool", "asset_in": "A", "asset_out": "B", "amount_in": 1, "min_amount_out": 0},
    )
    subclass = IntentSubclass(**vars(source))

    for foreign in (subclass, vars(source)):
        with pytest.raises(StateAdmissionError) as captured:
            snapshot_intent(foreign)  # type: ignore[arg-type]
        assert captured.value.code is AdmitCode.WRONG_EXACT_TYPE


def test_exact_registered_intent_source_union_and_owned_revalidation() -> None:
    swap = SwapIntent(
        "TauSwap",
        "0.1",
        IntentKind.SWAP_EXACT_IN,
        INTENT_ID,
        SENDER,
        9,
        None,
        {
            "pool_id": "pool",
            "asset_in": "A",
            "asset_out": "B",
            "amount_in": 1,
            "min_amount_out": 0,
        },
    )
    route = RouteIntent(
        "TauSwap",
        "0.1",
        IntentKind.ROUTE_EXACT_IN,
        INTENT_ID,
        SENDER,
        9,
        None,
        {
            "quote_receipt_hash": "0x" + "33" * 32,
            "asset_in": "A",
            "asset_out": "B",
            "leg_indices": [0],
            "total_amount_in": 1,
            "total_min_amount_out": 0,
        },
    )
    create_pool = CreatePoolIntent(
        "TauSwap",
        "0.1",
        IntentKind.CREATE_POOL,
        INTENT_ID,
        SENDER,
        9,
        None,
        {"asset0": "A", "asset1": "B", "fee_bps": 0, "amount0": 1, "amount1": 1},
    )
    validated = ValidatedIntent(**vars(_intent(IntentKind.ADD_LIQUIDITY, ALL_KIND_FIELDS[1][1])))

    for source in (swap, route, create_pool, validated):
        assert type(snapshot_intent(source)) is OwnedIntentV1

    owned = snapshot_intent(swap)
    reowned = snapshot_intent(owned)
    assert reowned == owned
    assert reowned is not owned


def test_exact_intent_with_undeclared_instance_attribute_rejects() -> None:
    source = _intent(IntentKind.CREATE_POOL, ALL_KIND_FIELDS[0][1])
    source.undeclared = "must reject"  # type: ignore[attr-defined]

    with pytest.raises(StateAdmissionError) as captured:
        snapshot_intent(source)

    assert captured.value.code is AdmitCode.UNKNOWN_FIELD
    assert captured.value.path == ()


def test_fcis_t_478_010_source_alias_mutation_does_not_change_owned_intent() -> None:
    leg_indices = [0, 2]
    source = _intent(
        IntentKind.ROUTE_EXACT_IN,
        {
            "asset_in": "A",
            "asset_out": "B",
            "leg_indices": leg_indices,
            "total_amount_in": 3,
            "total_min_amount_out": 2,
        },
    )
    owned = snapshot_intent(source)
    before = canonical_owned_intent_bytes_v1(owned)

    leg_indices.append(4)
    source.fields["asset_out"] = "C"

    assert canonical_owned_intent_bytes_v1(owned) == before
    assert not hasattr(owned, "set_field")
    assert Intent not in type(owned).__mro__


def test_fcis_t_478_012_and_013_intent_batch_is_owned_ordered_and_bounded() -> None:
    first = _intent(
        IntentKind.SWAP_EXACT_IN,
        {"pool_id": "pool", "asset_in": "A", "asset_out": "B", "amount_in": 1, "min_amount_out": 0},
    )
    second = _intent(
        IntentKind.SWAP_EXACT_OUT,
        {"pool_id": "pool", "asset_in": "A", "asset_out": "B", "amount_out": 1, "max_amount_in": 1},
    )
    source = [first, second]
    owned = admit_intent_batch(source)
    source.reverse()

    assert tuple(item.kind.member_ordinal for item in owned) == (3, 4)
    with pytest.raises(StateAdmissionError) as captured:
        admit_intent_batch([first] * 257)
    assert captured.value.code is AdmitCode.ITEM_LIMIT


def test_intent_batch_admits_boundaries_and_preserves_first_failure_precedence() -> None:
    valid = _intent(IntentKind.CREATE_POOL, ALL_KIND_FIELDS[0][1])
    assert admit_intent_batch([]) == ()
    assert len(admit_intent_batch([valid])) == 1
    assert len(admit_intent_batch([valid] * 256)) == 256

    invalid_first = _intent(IntentKind.CREATE_POOL, ALL_KIND_FIELDS[0][1])
    invalid_first.undeclared = 1  # type: ignore[attr-defined]
    with pytest.raises(StateAdmissionError) as captured:
        admit_intent_batch([invalid_first, object()])  # type: ignore[list-item]
    assert captured.value.code is AdmitCode.UNKNOWN_FIELD
    assert captured.value.path == (0,)


def test_intent_kind_member_order_is_schema_revision_pinned() -> None:
    assert tuple((member.name, member.value) for member in IntentKind) == (
        ("CREATE_POOL", "CREATE_POOL"),
        ("ADD_LIQUIDITY", "ADD_LIQUIDITY"),
        ("REMOVE_LIQUIDITY", "REMOVE_LIQUIDITY"),
        ("SWAP_EXACT_IN", "SWAP_EXACT_IN"),
        ("SWAP_EXACT_OUT", "SWAP_EXACT_OUT"),
        ("ROUTE_EXACT_IN", "ROUTE_EXACT_IN"),
        ("ROUTE_EXACT_OUT", "ROUTE_EXACT_OUT"),
    )


@pytest.mark.parametrize("kind", tuple(IntentKind))
def test_fcis_t_478_014_parser_and_owner_share_one_field_registry(kind: IntentKind) -> None:
    names = intent_allowed_field_names_v1(kind)
    assert len(names) == len(tuple(dict.fromkeys(names)))
    assert names[:7] == (
        "nonce",
        "recipient",
        "submission_order",
        "quote_receipt_hash",
        "quote_pool_fingerprint",
        "quote_receipt_leg_index",
        "oracle_authorization",
    )
