from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.global_settlement_types_v2 import canonical_global_bytes_v2
from src.core.perps_margin_state_v2 import (
    MAX_PERPS_MARGIN_ACCOUNTS_V2,
    PERPS_MARGIN_MODULE_SCHEMA_V2,
    PerpsMarginClaimBindingV2,
    PerpsMarginStateV2,
    margin_claim_id_v2,
)
from src.core.perps_margin_types_v1 import (
    PerpsMarginAccountStatusV1,
    PerpsMarginAccountV1,
    PerpsMarginStateV1,
)
from tests.core.test_perps_margin_module_v1 import (
    _account,
    _counterparty,
    _root,
    _state,
)


def _funded_state() -> PerpsMarginStateV1:
    return _state(
        accounts=(
            _account(collateral_atoms=10),
            _counterparty(collateral_atoms=20, position_base=0),
        )
    )


def _funded_claims() -> tuple[PerpsMarginClaimBindingV2, ...]:
    return (
        PerpsMarginClaimBindingV2("perps-account-1", _root(101)),
        PerpsMarginClaimBindingV2("perps-account-2", _root(102)),
    )


@pytest.mark.parametrize(
    "claims",
    (
        _funded_claims()[:1],
        (
            PerpsMarginClaimBindingV2("perps-account-1", _root(101)),
            PerpsMarginClaimBindingV2("perps-account-2", _root(101)),
        ),
        _funded_claims()[::-1],
        _funded_claims()
        + (PerpsMarginClaimBindingV2("perps-account-3", _root(103)),),
    ),
    ids=("missing", "shared", "unsorted", "dangling"),
)
def test_constructor_rejects_invalid_claim_coverage(
    claims: tuple[PerpsMarginClaimBindingV2, ...],
) -> None:
    with pytest.raises(ValueError):
        PerpsMarginStateV2(_funded_state(), claims)


@pytest.mark.parametrize(
    ("status", "account_id"),
    (
        (PerpsMarginAccountStatusV1.OPEN, "perps-account-1"),
        (PerpsMarginAccountStatusV1.CLOSED, "perps-account-2"),
    ),
)
def test_zero_collateral_open_and_closed_accounts_have_no_claim(
    status: PerpsMarginAccountStatusV1,
    account_id: str,
) -> None:
    account = replace(_account(collateral_atoms=0, status=status), account_id=account_id)
    state = PerpsMarginStateV2(_state(accounts=(account,)), ())
    assert state.claim_id(account_id) is None


def test_each_positive_collateral_account_has_exactly_one_claim() -> None:
    state = PerpsMarginStateV2(_funded_state(), _funded_claims())
    assert tuple(row.account_id for row in state.active_claims) == (
        "perps-account-1",
        "perps-account-2",
    )
    assert state.claim_id("perps-account-1") == _root(101)
    assert state.claim_id("perps-account-2") == _root(102)


def test_input_and_getter_snapshots_preserve_state_root() -> None:
    source_account = _account(collateral_atoms=9)
    source_state = _state(accounts=(source_account,))
    source_claim = PerpsMarginClaimBindingV2("perps-account-1", _root(101))
    state = PerpsMarginStateV2(source_state, (source_claim,))
    root = state.state_root

    object.__setattr__(source_state, "market_id", "perp-eth-usd")
    object.__setattr__(source_account, "collateral_atoms", 8)
    object.__setattr__(source_claim, "obligation_id", _root(102))
    getter_state = state.economic_state
    getter_claim = state.active_claims[0]
    object.__setattr__(getter_state, "market_id", "perp-eth-usd")
    object.__setattr__(getter_state.accounts[0], "collateral_atoms", 7)
    object.__setattr__(getter_claim, "obligation_id", _root(103))

    assert state.state_root == root
    assert state.economic_state.market_id == "perp-btc-usd"
    assert state.economic_state.accounts[0].collateral_atoms == 9
    assert state.claim_id("perps-account-1") == _root(101)


def test_scalar_subclasses_and_account_subclass_fail_before_hooks() -> None:
    class HostileText(str):
        def __bool__(self) -> bool:
            raise AssertionError("hostile scalar hook reached")

        def __len__(self) -> int:
            raise AssertionError("hostile scalar hook reached")

        def __iter__(self):
            raise AssertionError("hostile scalar hook reached")

    with pytest.raises(TypeError):
        PerpsMarginClaimBindingV2(HostileText("account"), _root(1))
    with pytest.raises(TypeError):
        PerpsMarginClaimBindingV2("account", HostileText(_root(2)))
    with pytest.raises(TypeError):
        PerpsMarginClaimBindingV2(True, _root(3))
    with pytest.raises(TypeError):
        PerpsMarginClaimBindingV2("account", True)

    class HostileAccount(PerpsMarginAccountV1):
        def __getattribute__(self, name: str) -> object:
            if name in {"account_id", "owner", "collateral_atoms"}:
                raise AssertionError("hostile account hook reached")
            return super().__getattribute__(name)

    base = _account(collateral_atoms=1)
    hostile = object.__new__(HostileAccount)
    for name in ("account_id", "owner", "position_base", "entry_price_e8", "collateral_atoms", "nonce", "status"):
        object.__setattr__(hostile, name, object.__getattribute__(base, name))
    malformed = _state(accounts=(base,))
    object.__setattr__(malformed, "accounts", (hostile,))
    with pytest.raises(TypeError):
        PerpsMarginStateV2(malformed, ())


def test_account_cardinality_accepts_64_and_rejects_65_before_walk() -> None:
    accounts = tuple(
        replace(_account(collateral_atoms=0), account_id=f"account-{index:02d}")
        for index in range(MAX_PERPS_MARGIN_ACCOUNTS_V2)
    )
    exact = PerpsMarginStateV2(_state(accounts=accounts), ())
    assert len(exact.economic_state.accounts) == 64

    too_many = _state(accounts=accounts)
    object.__setattr__(
        too_many,
        "accounts",
        accounts + (replace(_account(collateral_atoms=0), account_id="account-64"),),
    )
    with pytest.raises(ValueError, match="account count exceeds bound"):
        PerpsMarginStateV2(too_many, ())


def test_canonical_state_uses_successor_schema_only() -> None:
    state = PerpsMarginStateV2(_funded_state(), _funded_claims())
    canonical = state.to_canonical()
    encoded = canonical_global_bytes_v2(canonical)
    assert canonical["schema"] == PERPS_MARGIN_MODULE_SCHEMA_V2
    assert set(canonical) == set(_funded_state().to_canonical()) | {"active_claims"}
    assert b"zenodex/perps-margin-module/v2" in encoded
    assert b"zenodex/perps-margin-module/v1" not in encoded


@pytest.mark.parametrize(
    ("account_id", "occurrence_id", "state_kwargs"),
    (
        ("perps-account-1", _root(42), {}),
        ("perps-account-2", _root(41), {}),
        ("perps-account-1", _root(40), {"module_release_id": _root(4)}),
        ("perps-account-1", _root(40), {"market_id": "perp-eth-usd"}),
        ("perps-account-1", _root(40), {"collateral_asset": "TAU"}),
    ),
    ids=("occurrence", "account", "release", "market", "asset"),
)
def test_claim_id_changes_with_each_identity_coordinate(
    account_id: str,
    occurrence_id: str,
    state_kwargs: dict[str, object],
) -> None:
    state = _state()
    baseline = margin_claim_id_v2(state, "perps-account-1", _root(40))
    changed = margin_claim_id_v2(replace(state, **state_kwargs), account_id, occurrence_id)
    assert changed != baseline
