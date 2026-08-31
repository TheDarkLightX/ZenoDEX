from __future__ import annotations

from dataclasses import replace

import pytest

from src.core import (
    global_settlement_effect_plan_v2,
    global_settlement_effect_values_v2,
    global_settlement_lifecycle_v2,
    global_settlement_primitives_v2,
    global_settlement_types_v2,
)
from src.core.global_settlement_types_v1 import hash_global_v1
from src.core.global_settlement_types_v2 import (
    GLOBAL_SETTLEMENT_ABI_V2,
    MAX_ATOMS_V2,
    MAX_ORACLE_OCCURRENCE_DELTAS_PER_PLAN_V2,
    MAX_TERMINAL_OBLIGATION_DELTAS_PER_PLAN_V2,
    ZERO_ROOT_V2,
    AssetConservationRowV2,
    EconomicEffectKindV2,
    EconomicEffectRowV2,
    ExternalOutboxEnqueueV2,
    FeeConservationRowV2,
    GlobalEconomicEffectPlanV2,
    GlobalOracleOccurrencePlanV2,
    GlobalTerminalObligationPlanV2,
    LaneIdV2,
    LaneWriteV2,
    OracleOccurrenceDeltaV2,
    OracleOccurrenceStateV2,
    TerminalObligationDeltaV2,
    TerminalObligationStatusV2,
    TerminalObligationV2,
    canonical_global_bytes_v2,
    hash_global_v2,
)


def _root(label: str) -> str:
    return hash_global_v2("test-root-v2", {"label": label})


def _obligation(
    obligation_id: str = "obligation:1",
    *,
    amount_atoms: int = 10,
    status: TerminalObligationStatusV2 = TerminalObligationStatusV2.OPEN,
) -> TerminalObligationV2:
    return TerminalObligationV2(
        obligation_id=obligation_id,
        lane_id=LaneIdV2.PERPS_MARKET,
        claimant="alice",
        asset="USD",
        liability_domain="perps:margin",
        amount_atoms=amount_atoms,
        status=status,
    )


def _oracle(oracle_id: str = "oracle:1", *, height: int = 7) -> OracleOccurrenceStateV2:
    return OracleOccurrenceStateV2(
        oracle_id=oracle_id,
        occurrence_root=_root(f"occurrence:{oracle_id}:{height}"),
        observed_height=height,
        finalized=True,
    )


def test_v2_compatibility_facade_reexports_exact_implementation_objects() -> None:
    implementation_modules = (
        global_settlement_primitives_v2,
        global_settlement_lifecycle_v2,
        global_settlement_effect_values_v2,
        global_settlement_effect_plan_v2,
    )

    for implementation_module in implementation_modules:
        for exported_name in implementation_module.__all__:
            assert exported_name in global_settlement_types_v2.__all__
            assert getattr(global_settlement_types_v2, exported_name) is getattr(
                implementation_module,
                exported_name,
            )


def test_v2_hash_domain_is_disjoint_from_v1_for_the_same_payload() -> None:
    payload = {"asset": "USD", "amount_atoms": 1}

    assert canonical_global_bytes_v2(payload) == (b'{"amount_atoms":1,"asset":"USD"}')
    assert hash_global_v2("shared-shape", payload) != hash_global_v1(
        "shared-shape",
        payload,
    )
    assert GLOBAL_SETTLEMENT_ABI_V2.endswith("/v2")


def test_canonical_encoder_rejects_scalar_and_sequence_subclasses() -> None:
    class HostileInt(int):
        pass

    class HostileTuple(tuple[object, ...]):
        pass

    with pytest.raises(TypeError, match="scalar subclasses"):
        canonical_global_bytes_v2(HostileInt(1))
    with pytest.raises(TypeError, match="sequence subclasses"):
        canonical_global_bytes_v2(HostileTuple(("x",)))


def test_root_validation_rejects_ascii_whitespace_disguised_as_hex() -> None:
    malformed_root = "0x" + ("11" * 31) + "  "

    with pytest.raises(ValueError, match="canonical lowercase"):
        OracleOccurrenceStateV2(
            oracle_id="oracle:1",
            occurrence_root=malformed_root,
            observed_height=1,
            finalized=False,
        )


def test_terminal_obligation_identity_includes_liability_domain() -> None:
    before = _obligation()
    after = replace(before, amount_atoms=7)
    delta = TerminalObligationDeltaV2(before.obligation_id, before, after)
    plan = GlobalTerminalObligationPlanV2((delta,))

    assert plan.plan_root != ZERO_ROOT_V2
    with pytest.raises(ValueError, match="identity fields are immutable"):
        TerminalObligationDeltaV2(
            before.obligation_id,
            before,
            replace(after, liability_domain="other:liability"),
        )


def test_terminal_obligation_creation_and_terminal_transition_are_closed() -> None:
    created = _obligation()
    assert TerminalObligationDeltaV2(created.obligation_id, None, created)

    terminal = replace(created, status=TerminalObligationStatusV2.DRAINED)
    assert TerminalObligationDeltaV2(created.obligation_id, created, terminal)
    with pytest.raises(ValueError, match="must begin open"):
        TerminalObligationDeltaV2(terminal.obligation_id, None, terminal)
    with pytest.raises(ValueError, match="preserve the final open amount"):
        TerminalObligationDeltaV2(
            created.obligation_id,
            created,
            replace(terminal, amount_atoms=9),
        )


def test_open_terminal_obligation_requires_a_positive_amount() -> None:
    with pytest.raises(ValueError, match="open terminal obligation amount must be positive"):
        _obligation(amount_atoms=0)


def test_terminal_plan_empty_root_and_bound_are_exact() -> None:
    assert GlobalTerminalObligationPlanV2.empty().plan_root == ZERO_ROOT_V2
    deltas = tuple(
        TerminalObligationDeltaV2(
            f"obligation:{index:03d}",
            None,
            _obligation(f"obligation:{index:03d}"),
        )
        for index in range(MAX_TERMINAL_OBLIGATION_DELTAS_PER_PLAN_V2 + 1)
    )
    with pytest.raises(ValueError, match="bounded shape"):
        GlobalTerminalObligationPlanV2(deltas)


def test_terminal_plan_owns_nested_delta_snapshots() -> None:
    post = _obligation()
    delta = TerminalObligationDeltaV2(post.obligation_id, None, post)
    plan = GlobalTerminalObligationPlanV2((delta,))
    root = plan.plan_root

    object.__setattr__(post, "amount_atoms", 99)
    object.__setattr__(delta.post_obligation, "amount_atoms", 88)

    assert plan.plan_root == root
    assert plan.deltas[0].post_obligation.amount_atoms == 10


def test_terminal_plan_getter_returns_a_deep_snapshot() -> None:
    post = _obligation()
    plan = GlobalTerminalObligationPlanV2(
        (TerminalObligationDeltaV2(post.obligation_id, None, post),)
    )
    root = plan.plan_root

    borrowed = plan.deltas[0]
    object.__setattr__(borrowed.post_obligation, "amount_atoms", 99)

    assert plan.plan_root == root
    assert plan.deltas[0].post_obligation.amount_atoms == 10


def test_oracle_plan_binds_pre_and_post_occurrence() -> None:
    before = _oracle(height=7)
    after = _oracle(height=8)
    delta = OracleOccurrenceDeltaV2(before.oracle_id, before, after)
    plan = GlobalOracleOccurrencePlanV2((delta,))

    assert plan.plan_root != ZERO_ROOT_V2
    with pytest.raises(ValueError, match="height cannot regress"):
        OracleOccurrenceDeltaV2(before.oracle_id, after, before)
    with pytest.raises(ValueError, match="immutable at one observed height"):
        OracleOccurrenceDeltaV2(
            before.oracle_id,
            before,
            replace(before, occurrence_root=_root("other-occurrence")),
        )
    with pytest.raises(ValueError, match="finality cannot regress"):
        OracleOccurrenceDeltaV2(
            before.oracle_id,
            before,
            replace(after, finalized=False),
        )


def test_oracle_plan_getter_returns_a_deep_snapshot() -> None:
    before = _oracle(height=7)
    after = _oracle(height=8)
    plan = GlobalOracleOccurrencePlanV2(
        (OracleOccurrenceDeltaV2(before.oracle_id, before, after),)
    )
    root = plan.plan_root

    borrowed = plan.deltas[0]
    object.__setattr__(borrowed.post_occurrence, "observed_height", 99)

    assert plan.plan_root == root
    assert plan.deltas[0].post_occurrence.observed_height == 8


def test_economic_effect_plan_getters_return_deep_snapshots() -> None:
    occurrence_id = _root("occurrence-consumption")
    plan = GlobalEconomicEffectPlanV2(
        rows=(
            EconomicEffectRowV2(
                kind=EconomicEffectKindV2.ACCOUNT_MOVEMENT,
                principal="alice",
                asset="USD",
                custody_domain="account",
                delta_atoms=1,
            ),
        ),
        asset_conservation=(
            AssetConservationRowV2(
                asset="USD",
                owned_and_custodied_pre_atoms=1,
                owned_and_custodied_post_atoms=1,
                supply_pre_atoms=1,
                supply_post_atoms=1,
                authorized_issue_atoms=0,
                authorized_burn_atoms=0,
            ),
        ),
        fee_conservation=(FeeConservationRowV2("USD", 0, 0, 0),),
        lane_writes=(
            LaneWriteV2(LaneIdV2.ASSET_TRANSFER, _root("pre"), _root("post")),
        ),
        occurrence_consumptions=(occurrence_id,),
        external_outbox_enqueue=(
            ExternalOutboxEnqueueV2(
                effect_id=_root("effect"),
                destination_id="external:destination",
                payload_hash=_root("payload"),
                adapter_profile_root=_root("adapter"),
            ),
        ),
    )
    root = plan.effect_plan_root

    object.__setattr__(plan.rows[0], "delta_atoms", 99)
    object.__setattr__(plan.asset_conservation[0], "supply_post_atoms", 99)
    object.__setattr__(plan.fee_conservation[0], "fee_charged_atoms", 99)
    object.__setattr__(plan.lane_writes[0], "post_root", _root("forged-post"))
    object.__setattr__(
        plan.external_outbox_enqueue[0],
        "payload_hash",
        _root("forged-payload"),
    )

    assert plan.effect_plan_root == root
    assert plan.rows[0].delta_atoms == 1
    assert plan.asset_conservation[0].supply_post_atoms == 1
    assert plan.fee_conservation[0].fee_charged_atoms == 0
    assert plan.lane_writes[0].post_root == _root("post")
    assert plan.occurrence_consumptions == (occurrence_id,)
    assert plan.external_outbox_enqueue[0].payload_hash == _root("payload")


def test_cancelling_issue_and_burn_at_u128_max_is_valid() -> None:
    assert AssetConservationRowV2(
        asset="USD",
        owned_and_custodied_pre_atoms=MAX_ATOMS_V2,
        owned_and_custodied_post_atoms=MAX_ATOMS_V2,
        supply_pre_atoms=MAX_ATOMS_V2,
        supply_post_atoms=MAX_ATOMS_V2,
        authorized_issue_atoms=1,
        authorized_burn_atoms=1,
    )


def test_oracle_plan_empty_root_and_bound_are_exact() -> None:
    assert GlobalOracleOccurrencePlanV2.empty().plan_root == ZERO_ROOT_V2
    deltas = tuple(
        OracleOccurrenceDeltaV2(
            f"oracle:{index:03d}",
            None,
            _oracle(f"oracle:{index:03d}"),
        )
        for index in range(MAX_ORACLE_OCCURRENCE_DELTAS_PER_PLAN_V2 + 1)
    )
    with pytest.raises(ValueError, match="bounded shape"):
        GlobalOracleOccurrencePlanV2(deltas)


def test_plan_dataclass_replace_preserves_canonical_values_and_private_ownership() -> None:
    terminal = GlobalTerminalObligationPlanV2(
        (
            TerminalObligationDeltaV2(
                "obligation:1",
                None,
                _obligation(),
            ),
        )
    )
    oracle = GlobalOracleOccurrencePlanV2(
        (
            OracleOccurrenceDeltaV2(
                "oracle:1",
                None,
                _oracle(),
            ),
        )
    )
    effects = GlobalEconomicEffectPlanV2.empty()

    for plan in (terminal, oracle, effects):
        copied = replace(plan)
        assert copied == plan
        assert canonical_global_bytes_v2(copied.to_canonical()) == canonical_global_bytes_v2(
            plan.to_canonical()
        )
        assert copied is not plan
