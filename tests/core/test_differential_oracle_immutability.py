"""Regression bindings for the V4 differential-oracle alias cases."""

from __future__ import annotations

import copy
import inspect
import pickle
import sys
from collections.abc import Iterator, Mapping, Sequence
from dataclasses import FrozenInstanceError, is_dataclass, replace

import pytest

from src.core.batch_clearing import compute_settlement
from src.core.dex import DexEffects, DexState
from src.core.dex_intent_auth_message import hash_dex_intent_auth_message_v1
from src.core.settlement import Fill, FillAction, Settlement
from src.integration.zeno_oracle_settlement_authorization import normalized_settlement_hash
from src.state.balances import BalanceTable, FrozenBalanceTable
from src.state.canonical import canonical_json_bytes
from src.state.immutable import FrozenDict, FrozenSequence, SealedValue, deep_freeze
from src.state.intents import Intent, IntentKind
from src.state.lp import LPTable
from src.state.nonces import NonceTable
from src.state.pools import PoolState, PoolStatus
from src.state.state_root import compute_state_root

PUBKEY = "0x" + "11" * 48
ASSET0 = "0x" + "01" * 32
ASSET1 = "0x" + "02" * 32
POOL_ID = "0x" + "aa" * 32
INTENT_ID = "0x" + "bb" * 32


def _pool() -> PoolState:
    return PoolState(
        pool_id=POOL_ID,
        asset0=ASSET0,
        asset1=ASSET1,
        reserve0=1_000,
        reserve1=2_000,
        fee_bps=30,
        lp_supply=1_000,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


def _root(state: DexState) -> str:
    return compute_state_root(
        balances=state.balances,
        pools=state.pools,
        lp_balances=state.lp_balances,
        nonces=state.nonces,
    )


def _state(
    *,
    balances: BalanceTable | None = None,
    pools: dict[str, PoolState] | None = None,
    lp_balances: LPTable | None = None,
    nonces: NonceTable | None = None,
) -> DexState:
    return DexState(
        balances=balances or BalanceTable(),
        pools=pools or {},
        lp_balances=lp_balances or LPTable(),
        nonces=nonces or NonceTable(),
    )


def test_state_alias_001_balance_snapshot_is_owned_and_immutable() -> None:
    balances = BalanceTable()
    balances.set(PUBKEY, ASSET0, 10)
    state = _state(balances=balances)
    root_before = _root(state)

    balances.set(PUBKEY, ASSET0, 99)

    assert state.balances.get(PUBKEY, ASSET0) == 10
    assert _root(state) == root_before
    with pytest.raises(TypeError, match="cannot be mutated"):
        state.balances.set(PUBKEY, ASSET0, 77)


def test_state_alias_002_pool_mapping_and_values_are_owned_and_immutable() -> None:
    pool = _pool()
    pools = {POOL_ID: pool}
    state = _state(pools=pools)
    root_before = _root(state)

    pool.reserve0 = 77
    pools.clear()

    assert state.pools[POOL_ID].reserve0 == 1_000
    assert _root(state) == root_before
    with pytest.raises(TypeError, match="cannot be mutated"):
        state.pools[POOL_ID].reserve0 = 88
    with pytest.raises(TypeError, match="immutable value"):
        state.pools.clear()  # type: ignore[attr-defined]


def test_state_alias_003_lp_snapshot_includes_duration_metadata() -> None:
    lp = LPTable()
    lp.set(PUBKEY, POOL_ID, 10)
    lp.set_last_mint_timestamp(PUBKEY, POOL_ID, 7)
    lp.set_last_remove_timestamp(PUBKEY, POOL_ID, 5)
    lp.set_churn_tier(PUBKEY, POOL_ID, 2)
    lp.set_last_churn_update_timestamp(PUBKEY, POOL_ID, 6)
    state = _state(lp_balances=lp)
    root_before = _root(state)

    lp.set(PUBKEY, POOL_ID, 99)
    lp.set_churn_tier(PUBKEY, POOL_ID, 9)

    assert state.lp_balances.get(PUBKEY, POOL_ID) == 10
    assert state.lp_balances.get_duration_risk_metadata(PUBKEY, POOL_ID).churn_tier == 2
    assert _root(state) == root_before
    with pytest.raises(TypeError, match="cannot be mutated"):
        state.lp_balances.set(PUBKEY, POOL_ID, 77)


def test_state_alias_004_nonce_snapshot_cannot_change_replay_eligibility() -> None:
    nonces = NonceTable()
    nonces.set_last(PUBKEY, 1)
    state = _state(nonces=nonces)
    root_before = _root(state)

    nonces.set_last(PUBKEY, 2)

    assert state.nonces.get_last(PUBKEY) == 1
    assert _root(state) == root_before
    with pytest.raises(TypeError, match="cannot be mutated"):
        state.nonces.set_last(PUBKEY, 3)


def test_state_alias_005_intent_owns_transitively_immutable_signed_fields() -> None:
    path = [ASSET0, ASSET1]
    fields = {"amount_in": 100, "path": path}
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=INTENT_ID,
        sender_pubkey=PUBKEY,
        deadline=100,
        fields=fields,
    )
    digest_before = hash_dex_intent_auth_message_v1(intent, chain_id="audit-chain")

    fields["amount_in"] = 999
    path.append(ASSET0)

    assert intent.get_field("amount_in") == 100
    assert intent.get_field("path") == [ASSET0, ASSET1]
    assert hash_dex_intent_auth_message_v1(intent, chain_id="audit-chain") == digest_before
    with pytest.raises(TypeError, match="immutable value"):
        intent.fields["amount_in"] = 1  # type: ignore[index]
    with pytest.raises(TypeError):
        dict.__setitem__(intent.fields, "amount_in", 1)  # type: ignore[arg-type]
    with pytest.raises(AttributeError):
        intent.get_field("path").append(ASSET0)


def test_state_alias_006_effect_plan_owns_immutable_settlement() -> None:
    event = {"type": "AUDIT", "amounts": [1, 2]}
    proposal = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="batch-1",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
        events=[event],
    )
    effects = DexEffects(settlement=proposal, total_swap_fees=0)
    digest_before = normalized_settlement_hash(effects.settlement)

    event["amounts"].append(3)

    assert effects.settlement is not proposal
    assert normalized_settlement_hash(effects.settlement) == digest_before
    with pytest.raises(FrozenInstanceError):
        effects.settlement.batch_ref = "tampered"
    with pytest.raises(AttributeError):
        effects.settlement.events.append({"type": "TAMPER"})  # type: ignore[union-attr]
    with pytest.raises(TypeError, match="immutable value"):
        effects.settlement.events[0]["type"] = "TAMPER"  # type: ignore[index,union-attr]


def test_intent_reseals_prebuilt_frozen_wrapper_contents() -> None:
    retained_path = [ASSET0, ASSET1]
    adversarial_wrapper = FrozenDict({"amount_in": 100, "path": retained_path})

    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=INTENT_ID,
        sender_pubkey=PUBKEY,
        deadline=100,
        fields=adversarial_wrapper,
    )
    retained_path.append(ASSET0)

    assert intent.get_field("path") == [ASSET0, ASSET1]
    with pytest.raises(AttributeError):
        intent.get_field("path").append(ASSET0)


def test_settlement_reseals_prebuilt_frozen_wrapper_contents() -> None:
    retained_amounts = [1, 2]
    adversarial_event = FrozenDict({"type": "AUDIT", "amounts": retained_amounts})
    adversarial_events = FrozenSequence([adversarial_event])

    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="batch-1",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
        events=adversarial_events,
    )
    retained_amounts.append(3)

    assert settlement.events is not None
    assert settlement.events[0]["amounts"] == [1, 2]
    with pytest.raises(AttributeError):
        settlement.events[0]["amounts"].append(3)


def test_sealed_dataclass_blocks_ordinary_reinitialization_and_reconstruction() -> None:
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=INTENT_ID,
        sender_pubkey=PUBKEY,
        deadline=100,
        fields={"amount_in": 100},
    )
    digest_before = hash_dex_intent_auth_message_v1(intent, chain_id="audit-chain")

    assert not hasattr(intent, "__dict__")
    assert not hasattr(Intent.__init__, "__wrapped__")
    assert "module" in inspect.signature(Intent).parameters
    assert copy.copy(intent) is intent
    assert copy.deepcopy(intent) is intent
    with pytest.raises(TypeError, match="already initialized"):
        Intent.__init__(
            intent,
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=INTENT_ID,
            sender_pubkey=PUBKEY,
            deadline=100,
            fields={"amount_in": 999},
        )
    with pytest.raises(TypeError, match="canonical protocol encoder"):
        pickle.dumps(intent)
    with pytest.raises(TypeError, match="canonical protocol encoder"):
        intent.__setstate__([])  # type: ignore[attr-defined]

    assert hash_dex_intent_auth_message_v1(intent, chain_id="audit-chain") == digest_before
    changed = replace(intent, deadline=101)
    assert changed is not intent
    assert changed.deadline == 101
    with pytest.raises(TypeError, match="already initialized"):
        changed.__init__(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=INTENT_ID,
            sender_pubkey=PUBKEY,
            deadline=102,
            fields={"amount_in": 100},
        )

    fill = Fill(intent_id=INTENT_ID, action=FillAction.FILL, fee_paid=1)
    assert not hasattr(fill, "__dict__")
    with pytest.raises(TypeError, match="already initialized"):
        Fill.__init__(fill, intent_id=INTENT_ID, action=FillAction.FILL, fee_paid=999)
    assert fill.fee_paid == 1


def test_sealed_state_and_child_wrappers_reject_initializer_reentry() -> None:
    balances = BalanceTable()
    balances.set(PUBKEY, ASSET0, 10)
    lp = LPTable()
    lp.set(PUBKEY, POOL_ID, 10)
    nonces = NonceTable()
    nonces.set_last(PUBKEY, 1)
    state = _state(
        balances=balances,
        pools={POOL_ID: _pool()},
        lp_balances=lp,
        nonces=nonces,
    )
    root_before = _root(state)

    with pytest.raises(TypeError, match="already initialized"):
        state.pools.__init__({})
    with pytest.raises(TypeError, match="already initialized"):
        state.balances.__init__(BalanceTable())
    with pytest.raises(TypeError, match="already initialized"):
        state.lp_balances.__init__(LPTable())
    with pytest.raises(TypeError, match="already initialized"):
        state.nonces.__init__(NonceTable())
    with pytest.raises(TypeError, match="already initialized"):
        state.pools[POOL_ID].__init__(
            pool_id=POOL_ID,
            asset0=ASSET0,
            asset1=ASSET1,
            reserve0=1,
            reserve1=2_000,
            fee_bps=30,
            lp_supply=1_000,
            status=PoolStatus.ACTIVE,
            created_at=0,
        )
    with pytest.raises(TypeError, match="already initialized"):
        state.__init__(balances=BalanceTable(), pools={}, lp_balances=LPTable())

    assert _root(state) == root_before


def test_behavior_changing_subclasses_are_rejected_at_authority_boundaries() -> None:
    class ForgedBalanceTable(FrozenBalanceTable):
        def get(self, pubkey: str, asset: str) -> int:
            return 999

    balances = BalanceTable()
    balances.set(PUBKEY, ASSET0, 10)
    forged_balances = ForgedBalanceTable(balances)
    with pytest.raises(TypeError, match="exact BalanceTable snapshot"):
        _state(balances=forged_balances)

    class ForgedIntent(Intent):
        def get_field(self, key: str, default: object = None) -> object:
            if key == "amount_in":
                return 999
            return Intent.get_field(self, key, default)

    forged_intent = ForgedIntent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=INTENT_ID,
        sender_pubkey=PUBKEY,
        deadline=100,
        fields={"amount_in": 100},
    )
    with pytest.raises(TypeError, match="exact ZenoDEX intent"):
        hash_dex_intent_auth_message_v1(forged_intent, chain_id="audit-chain")
    with pytest.raises(TypeError, match="exact ZenoDEX intent"):
        compute_settlement(
            intents=[forged_intent],
            pools={},
            balances=BalanceTable(),
            lp_balances=LPTable(),
        )


def test_intent_rejects_mutable_salt_and_pool_rejects_status_lookalike() -> None:
    with pytest.raises(TypeError, match="salt"):
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=INTENT_ID,
            sender_pubkey=PUBKEY,
            deadline=100,
            salt=["mutable"],  # type: ignore[arg-type]
            fields={"amount_in": 100},
        )

    class StatusLookalike:
        value = "ACTIVE"

    with pytest.raises(TypeError, match="exact PoolStatus"):
        replace(_pool(), status=StatusLookalike())  # type: ignore[arg-type]


def test_settlement_consumes_untrusted_sequences_exactly_once() -> None:
    fill = Fill(intent_id=INTENT_ID, action=FillAction.REJECT, reason="audit")

    class OnePassFills(Sequence[Fill]):
        def __init__(self) -> None:
            self.iterations = 0

        def __len__(self) -> int:
            return 1

        def __getitem__(self, index: int) -> Fill:
            if index == 0:
                return fill
            raise IndexError(index)

        def __iter__(self) -> Iterator[Fill]:
            self.iterations += 1
            if self.iterations > 1:
                raise AssertionError("sequence traversed more than once")
            return iter((fill,))

    source = OnePassFills()
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="one-pass",
        included_intents=[(INTENT_ID, FillAction.REJECT)],
        fills=source,
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
    )

    assert source.iterations == 1
    assert settlement.fills == [fill]


@pytest.mark.parametrize("bad_value", [1.5, b"bytes", {"set-member"}])
def test_deep_freeze_rejects_noncanonical_json_values(bad_value: object) -> None:
    with pytest.raises(TypeError, match="non-canonical"):
        deep_freeze({"bad": bad_value})


def test_deep_freeze_rejects_non_string_keys_and_cycles() -> None:
    with pytest.raises(TypeError, match="keys must be exact strings"):
        deep_freeze({1: "bad-key"})
    cycle: list[object] = []
    cycle.append(cycle)
    with pytest.raises(TypeError, match="container cycle"):
        deep_freeze(cycle)


def test_canonical_json_projects_stateful_mapping_once_before_validation() -> None:
    class FlipMapping(Mapping[str, object]):
        def __init__(self) -> None:
            self.items_calls = 0

        def __getitem__(self, key: str) -> object:
            if key != "x":
                raise KeyError(key)
            return 0

        def __iter__(self) -> Iterator[str]:
            return iter(("x",))

        def __len__(self) -> int:
            return 1

        def items(self):  # type: ignore[no-untyped-def]
            self.items_calls += 1
            value: object = 0 if self.items_calls == 1 else 1.5
            return (("x", value),)

    value = FlipMapping()
    assert canonical_json_bytes(value) == b'{"x":0}'
    assert value.items_calls == 1


def test_every_loaded_sealed_dataclass_has_its_own_guard_and_slots() -> None:
    pending = list(SealedValue.__subclasses__())
    seen: set[type[object]] = set()
    while pending:
        cls = pending.pop()
        if cls in seen:
            continue
        seen.add(cls)
        pending.extend(cls.__subclasses__())
        if not is_dataclass(cls):
            continue
        # dataclass(slots=True) creates an unreachable precursor class that
        # remains visible through __subclasses__; audit the exported runtime
        # class, not that implementation artifact.
        if getattr(sys.modules[cls.__module__], cls.__name__, None) is not cls:
            continue
        assert cls.__dict__.get("__zenodex_init_guarded__") is True, cls.__qualname__
        assert "__slots__" in cls.__dict__, cls.__qualname__
