from __future__ import annotations

from dataclasses import fields as dataclass_fields
from dataclasses import replace
from typing import Any, cast

import pytest

from src.core.global_settlement_types_v1 import MAX_DELTA_ATOMS_V1, ZERO_ROOT_V1
from src.core.zdex_atomic_buyback_quote_port_v2 import ZDEXAtomicBuybackQuotePortV2
from src.core.zdex_fee_allocation_types_v1 import FEE_BUYBACK_PRINCIPAL_V1
from src.core.zdex_purchase_burn_route_types_v1 import zdex_pool_reserve_principal_v1


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _port() -> ZDEXAtomicBuybackQuotePortV2:
    return ZDEXAtomicBuybackQuotePortV2(
        profile_root=_root(1),
        route_release_id=_root(2),
        command_occurrence_id=_root(3),
        global_pre_state_root=_root(4),
        producer_module_release_id=_root(5),
        consumer_module_release_id=_root(6),
        producer_quote_pre_state_root=_root(7),
        producer_quote_post_state_root=_root(8),
        producer_quote_effect_plan_root=_root(9),
        selected_pool_id=_root(10),
        quote_asset_id=_root(11),
        amount_atoms=12,
    )


def _unchecked_replace(
    value: ZDEXAtomicBuybackQuotePortV2,
    **updates: object,
) -> ZDEXAtomicBuybackQuotePortV2:
    forged = object.__new__(ZDEXAtomicBuybackQuotePortV2)
    for field in dataclass_fields(value):
        object.__setattr__(
            forged,
            field.name,
            updates.get(field.name, object.__getattribute__(value, field.name)),
        )
    return forged


def test_port_derives_principals_and_excludes_proof_dependent_coordinates() -> None:
    # Arrange.
    port = _port()

    # Act.
    canonical = port.to_canonical()

    # Assert.
    assert port.source_principal == FEE_BUYBACK_PRINCIPAL_V1
    assert port.destination_principal == zdex_pool_reserve_principal_v1(
        pool_id=port.selected_pool_id,
        asset_id=port.quote_asset_id,
    )
    assert "source_principal" not in canonical
    assert "destination_principal" not in canonical
    assert "source_journal_root" not in canonical
    assert "source_receipt_binding_root" not in canonical


def test_port_root_binds_every_stored_coordinate() -> None:
    # Arrange.
    port = _port()
    replacements: dict[str, object] = {
        field.name: (
            port.amount_atoms + 1
            if field.name == "amount_atoms"
            else _root(100 + index)
        )
        for index, field in enumerate(dataclass_fields(port))
    }

    # Act / Assert.
    assert port.port_root == (
        "0xeabb1e68ae0540628753e32982bee5dc635bf41a70293185d6f3b1b3dffd4af4"
    )
    for field_name, replacement in replacements.items():
        assert replace(port, **cast(Any, {field_name: replacement})).port_root != port.port_root


@pytest.mark.parametrize("amount", (1, MAX_DELTA_ATOMS_V1))
def test_amount_boundaries_accept(amount: int) -> None:
    # Arrange / Act / Assert.
    assert replace(_port(), amount_atoms=amount).amount_atoms == amount


@pytest.mark.parametrize("amount", (0, MAX_DELTA_ATOMS_V1 + 1))
def test_amount_boundaries_reject(amount: int) -> None:
    # Arrange / Act / Assert.
    with pytest.raises(ValueError, match="positive signed effect"):
        replace(_port(), amount_atoms=amount)


@pytest.mark.parametrize(
    "updates",
    (
        {"producer_quote_effect_plan_root": "malformed"},
        {"producer_quote_effect_plan_root": ZERO_ROOT_V1},
        {"producer_quote_effect_plan_root": object()},
    ),
)
def test_retained_hostile_values_fail_before_hashing(updates: dict[str, object]) -> None:
    # Arrange.
    hostile = _unchecked_replace(_port(), **updates)

    # Act / Assert.
    with pytest.raises((TypeError, ValueError)):
        _ = hostile.port_root


def test_closed_constructor_rejects_unknown_fields() -> None:
    # Arrange.
    fields = {field.name: getattr(_port(), field.name) for field in dataclass_fields(_port())}

    # Act / Assert.
    with pytest.raises(TypeError, match="unexpected keyword"):
        cast(Any, ZDEXAtomicBuybackQuotePortV2)(
            **fields,
            source_receipt_binding_root=_root(99),
        )
