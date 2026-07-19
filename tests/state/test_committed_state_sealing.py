"""Adversarial regressions for the mutable-builder -> committed-state seal."""

from __future__ import annotations

from collections.abc import Iterator, Mapping

import pytest

from src.core.dex import DexState
from src.state.balances import BalanceTable, FrozenBalanceTable
from src.state.lp import FrozenLPTable, LPDurationRiskMetadata, LPTable
from src.state.nonces import FrozenNonceTable, NonceTable
from src.state.pools import FrozenPoolState, PoolState, PoolStatus

PK = "0x" + "11" * 48
PK_LOWER = "0x" + "ab" * 48
PK_UPPER = "0x" + "AB" * 48
ASSET0 = "0x" + "01" * 32
ASSET_LOWER = "0x" + "cd" * 32
ASSET_UPPER = "0x" + "CD" * 32
ASSET1 = "0x" + "02" * 32
POOL_ID = "0x" + "22" * 32
POOL_LOWER = "0x" + "ab" * 32
POOL_UPPER = "0x" + "AB" * 32


def _pool(pool_id: str = POOL_ID, *, reserve0: int = 100) -> PoolState:
    return PoolState(
        pool_id=pool_id,
        asset0=ASSET0,
        asset1=ASSET1,
        reserve0=reserve0,
        reserve1=200,
        fee_bps=30,
        lp_supply=100,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


def _state(
    *,
    balances: BalanceTable | None = None,
    pools: dict[str, PoolState] | None = None,
    lp_balances: LPTable | None = None,
    nonces: NonceTable | None = None,
) -> DexState:
    return DexState(
        balances=BalanceTable() if balances is None else balances,
        pools={} if pools is None else pools,
        lp_balances=LPTable() if lp_balances is None else lp_balances,
        nonces=NonceTable() if nonces is None else nonces,
    )


class _BehaviorChangingStr(str):
    """Textually stable, but mutable equality previously changed table lookups."""

    __hash__ = str.__hash__

    def __new__(cls, value: str) -> "_BehaviorChangingStr":
        result = super().__new__(cls, value)
        result.closed = False
        return result

    def __eq__(self, other: object) -> bool:
        if self.closed:
            return self is other
        return str.__eq__(self, other)


def test_state_key_builders_reject_behavior_changing_string_subclasses() -> None:
    forged_pk = _BehaviorChangingStr(PK)
    forged_pool_id = _BehaviorChangingStr(POOL_ID)

    with pytest.raises(TypeError, match="exact string"):
        BalanceTable().set(forged_pk, ASSET0, 10)
    with pytest.raises(TypeError, match="exact string"):
        LPTable().set(forged_pk, POOL_ID, 10)
    with pytest.raises(TypeError, match="exact string"):
        NonceTable().set_last(forged_pk, 1)
    with pytest.raises(TypeError, match="exact type"):
        _pool(forged_pool_id)


def test_balance_seal_revalidates_mutable_builder_internals() -> None:
    balances = BalanceTable()
    balances._balances[(PK, ASSET0)] = -1

    with pytest.raises(ValueError, match="stored balance amounts must be positive"):
        _state(balances=balances)


def test_lp_seal_revalidates_balances_and_duration_metadata() -> None:
    negative_balance = LPTable()
    negative_balance._balances[(PK, POOL_ID)] = -1
    with pytest.raises(ValueError, match="LP balance must be a non-negative int"):
        _state(lp_balances=negative_balance)

    negative_metadata = LPTable()
    negative_metadata.set(PK, POOL_ID, 1)
    negative_metadata._last_remove_timestamps[(PK, POOL_ID)] = -1
    with pytest.raises(ValueError, match="last remove timestamp must be a non-negative int"):
        _state(lp_balances=negative_metadata)

    orphaned_mint_age = LPTable()
    orphaned_mint_age._last_mint_timestamps[(PK, POOL_ID)] = 1
    with pytest.raises(ValueError, match="requires a positive LP balance"):
        _state(lp_balances=orphaned_mint_age)


def test_nonce_seal_revalidates_builder_range_and_spelling() -> None:
    out_of_range = NonceTable()
    out_of_range._last[PK] = 1 << 40
    with pytest.raises(TypeError, match="fit in u32"):
        _state(nonces=out_of_range)

    noncanonical = NonceTable()
    noncanonical._last[PK_UPPER] = 1
    with pytest.raises(ValueError, match="canonical lowercase wire form"):
        _state(nonces=noncanonical)


def test_lp_duration_record_rejects_non_exact_or_negative_numbers() -> None:
    with pytest.raises(TypeError, match="churn_tier must be an int"):
        LPDurationRiskMetadata(churn_tier=True)
    with pytest.raises(ValueError, match="last_remove_timestamp must be a non-negative int"):
        LPDurationRiskMetadata(last_remove_timestamp=-1)


def test_balance_seal_rejects_duplicate_decoded_identity_spellings() -> None:
    balances = BalanceTable()
    balances.set(PK_LOWER, ASSET_LOWER, 1)
    balances.set(PK_UPPER, ASSET_UPPER, 2)

    with pytest.raises(ValueError, match=r"duplicate decoded \(pubkey, asset\)"):
        _state(balances=balances)


def test_lp_seal_rejects_duplicate_decoded_identity_spellings_across_metadata() -> None:
    lp_balances = LPTable()
    lp_balances.set(PK_LOWER, POOL_LOWER, 1)
    lp_balances.set_last_remove_timestamp(PK_UPPER, POOL_UPPER, 2)

    with pytest.raises(ValueError, match=r"duplicate decoded \(pubkey, pool_id\)"):
        _state(lp_balances=lp_balances)


def test_pool_seal_rejects_duplicate_decoded_pool_id_spellings() -> None:
    pools = {
        POOL_LOWER: _pool(POOL_LOWER, reserve0=100),
        POOL_UPPER: _pool(POOL_UPPER, reserve0=200),
    }

    with pytest.raises(ValueError, match="duplicate decoded pool_id"):
        _state(pools=pools)


def test_pool_seal_rejects_nonconforming_mapping_with_duplicate_exact_items() -> None:
    first = _pool(reserve0=100)
    second = _pool(reserve0=200)

    class DuplicateItemsMapping(Mapping[str, PoolState]):
        def __getitem__(self, key: str) -> PoolState:
            if key != POOL_ID:
                raise KeyError(key)
            return first

        def __iter__(self) -> Iterator[str]:
            return iter((POOL_ID,))

        def __len__(self) -> int:
            return 1

        def items(self):  # type: ignore[no-untyped-def]
            return ((POOL_ID, first), (POOL_ID, second))

    with pytest.raises(ValueError, match="duplicate pool_id in pools mapping iteration"):
        DexState(
            balances=BalanceTable(),
            pools=DuplicateItemsMapping(),
            lp_balances=LPTable(),
        )


def test_uninitialized_frozen_wrapper_reconstruction_is_rejected() -> None:
    uninitialized_balances = FrozenBalanceTable.__new__(FrozenBalanceTable)
    with pytest.raises(TypeError, match="FrozenBalanceTable is not initialized"):
        _state(balances=uninitialized_balances)

    uninitialized_lp = FrozenLPTable.__new__(FrozenLPTable)
    with pytest.raises(TypeError, match="FrozenLPTable is not initialized"):
        _state(lp_balances=uninitialized_lp)

    uninitialized_nonces = FrozenNonceTable.__new__(FrozenNonceTable)
    with pytest.raises(TypeError, match="FrozenNonceTable is not initialized"):
        _state(nonces=uninitialized_nonces)

    uninitialized_pool = FrozenPoolState.__new__(FrozenPoolState)
    with pytest.raises(TypeError, match="FrozenPoolState is not initialized"):
        _state(pools={POOL_ID: uninitialized_pool})


def test_symbolic_nonproduction_identities_remain_compatible() -> None:
    balances = BalanceTable()
    balances.set("alice", "A", 10)
    lp_balances = LPTable()
    lp_balances.set("alice", "pool-a", 5)

    state = _state(
        balances=balances,
        pools={"pool-a": _pool("pool-a")},
        lp_balances=lp_balances,
    )

    assert state.balances.get("alice", "A") == 10
    assert state.lp_balances.get("alice", "pool-a") == 5
    assert state.pools["pool-a"].reserve0 == 100
