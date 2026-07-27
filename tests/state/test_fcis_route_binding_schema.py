"""Closed route child-schema admission tests for FCIS M5-P4B3."""

from __future__ import annotations

import pytest

from src.core.domain_limits import DEX_SWAP_AMOUNT_MAX
from src.state.fcis_route_binding_schema import (
    ROUTE_HASH_32_V1,
    ROUTE_LEG_SCHEMA_ID_V1,
    ROUTE_POOL_FINGERPRINTS_SCHEMA_ID_V1,
    ROUTE_TEXT_256_V1,
)
from src.state.intent_schema import HASH_32_V1, TEXT_256_V1
from src.state.intent_snapshots import OwnedIntentV1, snapshot_intent
from src.state.intents import Intent, IntentKind
from src.state.owned_collections import OwnedMapV1
from src.state.snapshot_combinators import AdmitCode
from src.state.state_snapshots import StateAdmissionError

INTENT_ID = "0x" + "11" * 32
SENDER = "0x" + "22" * 48
ASSET_IN = "0x" + "01" * 32
ASSET_OUT = "0x" + "02" * 32
POOL_A = "0x" + "aa" * 32
POOL_B = "0x" + "bb" * 32
FINGERPRINT_A = "0x" + "cc" * 32
FINGERPRINT_B = "0x" + "dd" * 32


def _leg(
    pool_id: str = POOL_A,
    amount_in: int = 10,
    amount_out: int = 9,
) -> dict[str, object]:
    return {
        "pool_id": pool_id,
        "asset_in": ASSET_IN,
        "asset_out": ASSET_OUT,
        "amount_in": amount_in,
        "amount_out": amount_out,
    }


def _route_fields(kind: IntentKind) -> dict[str, object]:
    fields: dict[str, object] = {
        "asset_in": ASSET_IN,
        "asset_out": ASSET_OUT,
        "leg_indices": [0],
        "route_legs": [_leg()],
        "route_pool_fingerprints": {POOL_A: FINGERPRINT_A},
    }
    if kind is IntentKind.ROUTE_EXACT_IN:
        fields["total_amount_in"] = 10
        fields["total_min_amount_out"] = 1
    else:
        fields["total_amount_out"] = 9
        fields["total_max_amount_in"] = 10
    return fields


def _route_intent(kind: IntentKind, fields: dict[str, object]) -> Intent:
    return Intent("TauSwap", "0.1", kind, INTENT_ID, SENDER, 9, None, fields)


def _admit_reject(intent: Intent) -> StateAdmissionError:
    with pytest.raises(StateAdmissionError) as captured:
        snapshot_intent(intent)
    return captured.value


def test_valid_exact_in_and_exact_out_route_fields_admit() -> None:
    exact_in = snapshot_intent(
        _route_intent(IntentKind.ROUTE_EXACT_IN, _route_fields(IntentKind.ROUTE_EXACT_IN))
    )
    exact_out = snapshot_intent(
        _route_intent(IntentKind.ROUTE_EXACT_OUT, _route_fields(IntentKind.ROUTE_EXACT_OUT))
    )

    for owned in (exact_in, exact_out):
        assert type(owned) is OwnedIntentV1
        legs = owned.fields["route_legs"]
        fingerprints = owned.fields["route_pool_fingerprints"]
        assert type(legs) is tuple and len(legs) == 1
        assert type(legs[0]) is OwnedMapV1
        assert legs[0].schema_id == ROUTE_LEG_SCHEMA_ID_V1
        assert legs[0].entries == (
            ("amount_in", 10),
            ("amount_out", 9),
            ("asset_in", ASSET_IN),
            ("asset_out", ASSET_OUT),
            ("pool_id", POOL_A),
        )
        assert type(fingerprints) is OwnedMapV1
        assert fingerprints.schema_id == ROUTE_POOL_FINGERPRINTS_SCHEMA_ID_V1
        assert fingerprints.entries == ((POOL_A, FINGERPRINT_A),)


def test_list_and_tuple_source_forms_produce_equal_owned_tuples() -> None:
    list_fields = _route_fields(IntentKind.ROUTE_EXACT_IN)
    tuple_fields = _route_fields(IntentKind.ROUTE_EXACT_IN)
    tuple_fields["route_legs"] = tuple(list_fields["route_legs"])  # type: ignore[arg-type]

    from_list = snapshot_intent(_route_intent(IntentKind.ROUTE_EXACT_IN, list_fields))
    from_tuple = snapshot_intent(_route_intent(IntentKind.ROUTE_EXACT_IN, tuple_fields))

    assert from_list.fields["route_legs"] == from_tuple.fields["route_legs"]
    assert from_list == from_tuple


def test_caller_mutation_after_admission_cannot_change_owned_route_graph() -> None:
    fields = _route_fields(IntentKind.ROUTE_EXACT_IN)
    legs = fields["route_legs"]
    fingerprints = fields["route_pool_fingerprints"]
    owned = snapshot_intent(_route_intent(IntentKind.ROUTE_EXACT_IN, fields))
    before = owned.fields["route_legs"], owned.fields["route_pool_fingerprints"]

    legs[0]["amount_in"] = 1  # type: ignore[index]
    legs.append(_leg(pool_id=POOL_B))  # type: ignore[attr-defined]
    fingerprints[POOL_B] = FINGERPRINT_B  # type: ignore[index]

    assert owned.fields["route_legs"] == before[0]
    assert owned.fields["route_pool_fingerprints"] == before[1]


def test_empty_and_over_budget_leg_sequences_reject_with_stable_code_and_path() -> None:
    empty = _route_fields(IntentKind.ROUTE_EXACT_IN)
    empty["route_legs"] = []
    reject = _admit_reject(_route_intent(IntentKind.ROUTE_EXACT_IN, empty))
    assert reject.code is AdmitCode.ITEM_LIMIT
    assert reject.path == ("fields", "route_legs")

    over_budget = _route_fields(IntentKind.ROUTE_EXACT_IN)
    over_budget["leg_indices"] = list(range(256))
    over_budget["route_legs"] = [_leg(amount_in=1, amount_out=1) for _ in range(257)]
    over_budget["total_amount_in"] = 256
    reject = _admit_reject(_route_intent(IntentKind.ROUTE_EXACT_IN, over_budget))
    assert reject.code is AdmitCode.ITEM_LIMIT
    assert reject.path == ("fields", "route_legs")

    over_indices = _route_fields(IntentKind.ROUTE_EXACT_IN)
    over_indices["leg_indices"] = list(range(257))
    over_indices["route_legs"] = [_leg(amount_in=1, amount_out=1) for _ in range(257)]
    over_indices["total_amount_in"] = 257
    reject = _admit_reject(_route_intent(IntentKind.ROUTE_EXACT_IN, over_indices))
    assert reject.code is AdmitCode.ITEM_LIMIT
    assert reject.path == ("fields", "leg_indices")


def test_leg_missing_extra_misspelled_and_duplicated_semantic_fields_reject() -> None:
    missing = _route_fields(IntentKind.ROUTE_EXACT_IN)
    missing["route_legs"] = [
        {"pool_id": POOL_A, "asset_in": ASSET_IN, "asset_out": ASSET_OUT, "amount_in": 10}
    ]
    reject = _admit_reject(_route_intent(IntentKind.ROUTE_EXACT_IN, missing))
    assert reject.code is AdmitCode.ITEM_LIMIT
    assert reject.path == ("fields", "route_legs", 0)

    extra = _route_fields(IntentKind.ROUTE_EXACT_IN)
    extra["route_legs"] = [{**_leg(), "fee_paid": 1}]
    reject = _admit_reject(_route_intent(IntentKind.ROUTE_EXACT_IN, extra))
    assert reject.code is AdmitCode.ITEM_LIMIT
    assert reject.path == ("fields", "route_legs", 0)

    misspelled = _route_fields(IntentKind.ROUTE_EXACT_IN)
    misspelled["route_legs"] = [
        {
            "pool_id": POOL_A,
            "asset_in": ASSET_IN,
            "asset_out": ASSET_OUT,
            "amount_in": 10,
            "amount_ouu": 9,
        }
    ]
    reject = _admit_reject(_route_intent(IntentKind.ROUTE_EXACT_IN, misspelled))
    assert reject.code is AdmitCode.UNKNOWN_FIELD
    assert reject.path == ("fields", "route_legs", 0, "amount_ouu")

    duplicated_semantics = _route_fields(IntentKind.ROUTE_EXACT_IN)
    duplicated_semantics["total_amount_out"] = 9
    reject = _admit_reject(_route_intent(IntentKind.ROUTE_EXACT_IN, duplicated_semantics))
    assert reject.code is AdmitCode.UNKNOWN_FIELD
    assert reject.path == ("fields", "total_amount_out")


def test_bool_amounts_reject() -> None:
    fields = _route_fields(IntentKind.ROUTE_EXACT_IN)
    fields["route_legs"] = [{**_leg(), "amount_in": True}]
    reject = _admit_reject(_route_intent(IntentKind.ROUTE_EXACT_IN, fields))
    assert reject.code is AdmitCode.WRONG_EXACT_TYPE
    assert reject.path == ("fields", "route_legs", 0, "amount_in")

    fields = _route_fields(IntentKind.ROUTE_EXACT_IN)
    fields["route_legs"] = [{**_leg(), "amount_out": False}]
    reject = _admit_reject(_route_intent(IntentKind.ROUTE_EXACT_IN, fields))
    assert reject.code is AdmitCode.WRONG_EXACT_TYPE
    assert reject.path == ("fields", "route_legs", 0, "amount_out")


def test_leg_amount_bounds_reject() -> None:
    for amount in (0, -1, DEX_SWAP_AMOUNT_MAX + 1):
        fields = _route_fields(IntentKind.ROUTE_EXACT_IN)
        fields["route_legs"] = [{**_leg(), "amount_in": amount}]
        reject = _admit_reject(_route_intent(IntentKind.ROUTE_EXACT_IN, fields))
        assert reject.code is AdmitCode.OUT_OF_RANGE
        assert reject.path == ("fields", "route_legs", 0, "amount_in")


def test_malformed_pool_ids_assets_and_fingerprints_reject() -> None:
    cases: tuple[tuple[dict[str, object], AdmitCode, tuple[str | int, ...]], ...] = ()
    empty_pool = _route_fields(IntentKind.ROUTE_EXACT_IN)
    empty_pool["route_legs"] = [{**_leg(), "pool_id": ""}]
    cases += ((empty_pool, AdmitCode.NONCANONICAL_SCALAR, ("fields", "route_legs", 0, "pool_id")),)
    long_pool = _route_fields(IntentKind.ROUTE_EXACT_IN)
    long_pool["route_legs"] = [{**_leg(), "pool_id": "p" * 257}]
    cases += ((long_pool, AdmitCode.BYTE_LIMIT, ("fields", "route_legs", 0, "pool_id")),)
    long_asset = _route_fields(IntentKind.ROUTE_EXACT_IN)
    long_asset["route_legs"] = [{**_leg(), "asset_in": "a" * 257}]
    cases += ((long_asset, AdmitCode.BYTE_LIMIT, ("fields", "route_legs", 0, "asset_in")),)
    for bad_fingerprint in ("cc" * 32, "0x" + "CC" * 32, "0x" + "cc" * 31, ""):
        bad = _route_fields(IntentKind.ROUTE_EXACT_IN)
        bad["route_pool_fingerprints"] = {POOL_A: bad_fingerprint}
        cases += (
            (
                bad,
                AdmitCode.NONCANONICAL_SCALAR,
                ("fields", "route_pool_fingerprints", POOL_A),
            ),
        )
    long_fingerprint = _route_fields(IntentKind.ROUTE_EXACT_IN)
    long_fingerprint["route_pool_fingerprints"] = {POOL_A: "0x" + "cc" * 33}
    cases += (
        (
            long_fingerprint,
            AdmitCode.BYTE_LIMIT,
            ("fields", "route_pool_fingerprints", POOL_A),
        ),
    )
    bool_fingerprint = _route_fields(IntentKind.ROUTE_EXACT_IN)
    bool_fingerprint["route_pool_fingerprints"] = {POOL_A: True}
    cases += (
        (
            bool_fingerprint,
            AdmitCode.WRONG_EXACT_TYPE,
            ("fields", "route_pool_fingerprints", POOL_A),
        ),
    )
    for fields, code, path in cases:
        reject = _admit_reject(_route_intent(IntentKind.ROUTE_EXACT_IN, fields))
        assert reject.code is code
        assert reject.path == path

    over_budget = _route_fields(IntentKind.ROUTE_EXACT_IN)
    over_budget["route_pool_fingerprints"] = {
        f"0x{index:064x}": FINGERPRINT_A for index in range(257)
    }
    reject = _admit_reject(_route_intent(IntentKind.ROUTE_EXACT_IN, over_budget))
    assert reject.code is AdmitCode.ITEM_LIMIT
    assert reject.path == ("fields", "route_pool_fingerprints")


def test_non_route_intents_cannot_carry_reserved_route_fields() -> None:
    swap_fields: dict[str, object] = {
        "pool_id": "pool",
        "asset_in": "A",
        "asset_out": "B",
        "amount_in": 1,
        "min_amount_out": 0,
    }
    for reserved in ("route_legs", "route_pool_fingerprints"):
        fields = dict(swap_fields)
        fields[reserved] = _route_fields(IntentKind.ROUTE_EXACT_IN)[reserved]
        reject = _admit_reject(_route_intent(IntentKind.SWAP_EXACT_IN, fields))
        assert reject.code is AdmitCode.UNKNOWN_FIELD
        assert reject.path == ("fields", reserved)


def test_route_primitive_rules_match_current_intent_field_rules() -> None:
    assert ROUTE_TEXT_256_V1 == TEXT_256_V1
    assert ROUTE_HASH_32_V1 == HASH_32_V1


def test_fingerprint_insertion_order_yields_one_canonical_owned_map() -> None:
    forward = _route_fields(IntentKind.ROUTE_EXACT_IN)
    forward["leg_indices"] = [0, 1]
    forward["route_legs"] = [
        _leg(pool_id=POOL_A, amount_in=4, amount_out=3),
        _leg(pool_id=POOL_B, amount_in=6, amount_out=5),
    ]
    forward["total_amount_in"] = 10
    forward["route_pool_fingerprints"] = {POOL_A: FINGERPRINT_A, POOL_B: FINGERPRINT_B}
    reverse = dict(forward)
    reverse["route_pool_fingerprints"] = {POOL_B: FINGERPRINT_B, POOL_A: FINGERPRINT_A}

    from_forward = snapshot_intent(_route_intent(IntentKind.ROUTE_EXACT_IN, forward))
    from_reverse = snapshot_intent(_route_intent(IntentKind.ROUTE_EXACT_IN, reverse))

    canonical_order = tuple(sorted((POOL_A, POOL_B)))
    assert (
        from_forward.fields["route_pool_fingerprints"]
        == from_reverse.fields["route_pool_fingerprints"]
    )
    assert (
        tuple(key for key, _value in from_forward.fields["route_pool_fingerprints"].entries)
        == canonical_order
    )


def test_owned_route_values_round_trip_through_readmission() -> None:
    owned = snapshot_intent(
        _route_intent(IntentKind.ROUTE_EXACT_IN, _route_fields(IntentKind.ROUTE_EXACT_IN))
    )

    reowned = snapshot_intent(owned)

    assert reowned == owned
    assert reowned is not owned
