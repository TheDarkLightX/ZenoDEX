# [TESTER] v1

from __future__ import annotations

from collections.abc import Callable
from dataclasses import replace
from typing import cast

import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

import src.core.fcis_step_evaluator as fcis_step_evaluator
import src.core.fcis_support_profile_v5 as fcis_support_profile_v5
from src.agents.intent_signer import create_route_intent_from_quote_receipt
from src.core.batch_clearing import compute_settlement
from src.core.dex import DexState
from src.core.fcis_state_read_trace_v5 import FCISStateReadTraceV5
from src.core.fcis_step_evaluation_values import (
    FCISStepEvaluationOkV1,
    FCISStepEvaluationPhaseV1,
    FCISStepEvaluationRejectV1,
)
from src.core.fcis_step_evaluator import evaluate_fcis_step_candidate_v1
from src.core.fcis_support_profile_v5 import (
    FCIS_CONTEXT_SCHEMA_PATHS_V5,
    FCIS_SUPPORT_COMMAND_ONLY_FIELDS_V5,
    FCIS_SUPPORT_CONTEXT_PATHS_V5,
    FCIS_SUPPORT_FIELD_DEPENDENCIES_V5,
    FCIS_SUPPORT_INTENT_FIELD_INVENTORY_V5,
    FCIS_SUPPORT_PROFILE_COMPLETE_V5,
    FCIS_SUPPORT_PROFILE_ID_V5,
    FCIS_SUPPORT_PROFILE_VERSION_V5,
    FCISSupportRootEvidenceV5,
    compute_fcis_support_root_v5,
    derive_fcis_support_set_v5,
)
from src.core.fcis_traced_reads_v5 import read_step_execution_context_v5
from src.core.fees import FeeAccumulatorState
from src.core.liquidity import create_pool
from src.core.oracle import OracleState
from src.core.perps import PERPS_STATE_VERSION_V4, PerpsState
from src.core.quote_receipts import make_route_quote_receipt
from src.core.route_settlement import resolve_route_binding_from_receipt, route_binding_to_fields
from src.core.routing import best_route_exact_in_2hop, best_route_exact_out_2hop
from src.core.settlement import FillAction, Settlement
from src.core.settlement_snapshots import snapshot_settlement
from src.core.vault import VaultState
from src.state import BalanceTable, LPTable
from src.state.canonical import domain_sep_bytes, encode_bytes
from src.state.fcis_committed_state_values import FCISCommittedStateSourceV1
from src.state.fcis_execution_context import admit_fcis_step_execution_context_v1
from src.state.fcis_execution_context_schema import (
    FCIS_FEE_SPLIT_POLICY_FIELD_NAMES_V1,
    FCIS_LP_DURATION_POLICY_FIELD_NAMES_V1,
    FCIS_SETTLEMENT_CONTEXT_FIELD_NAMES_V1,
)
from src.state.fcis_execution_context_values import (
    FCISFeeSplitPolicySourceV1,
    FCISSettlementExecutionContextSourceV1,
    FCISSettlementModeV1,
    FCISStepExecutionContextSourceV1,
    FCISStepExecutionContextV1,
)
from src.state.intent_field_registry import intent_allowed_field_names_v1
from src.state.intent_snapshots import OwnedIntentV1, admit_intent_batch
from src.state.intents import Intent, IntentKind
from src.state.legacy_state_snapshots import (
    admit_legacy_balance_for_differential_v1,
    admit_legacy_lp_for_differential_v1,
    admit_legacy_nonce_for_differential_v1,
    admit_legacy_pool_map_for_differential_v1,
)
from src.state.lp_duration_policy_schema import LPDurationPolicyAdmissionSourceV1
from src.state.nonces import NonceTable
from src.state.pools import PoolState
from src.state.snapshot_combinators import AdmitOk
from src.state.state_snapshots import (
    snapshot_fee_accumulator,
    snapshot_oracle,
    snapshot_perps,
    snapshot_vault,
)

SENDER = "0x" + "11" * 48
RECIPIENT = "0x" + "22" * 48
PROTOCOL = "0x" + "33" * 48
OTHER = "0x" + "44" * 48
ASSET0 = "0x" + "01" * 32
ASSET1 = "0x" + "02" * 32
OTHER_ASSET = "0x" + "03" * 32


def _iid(value: int) -> str:
    return "0x" + f"{value:064x}"


def test_v5_root_preimage_has_each_normative_section_once_in_order() -> None:
    digest = "0x" + "00" * 32
    sections = {
        "balances_section": b"balances",
        "pools_section": b"pools",
        "lp_section": b"lp",
        "nonce_section": b"nonce",
        "fee_section": b"fee",
    }

    observed = fcis_support_profile_v5._root_preimage_v5(
        command_root=digest,
        context_hash=digest,
        support_commitment=digest,
        **sections,
    )
    expected = bytearray(
        domain_sep_bytes(fcis_support_profile_v5.FCIS_SUPPORT_ROOT_DOMAIN_V5, version=5)
    )
    for label, payload in (
        (b"CMD", bytes(32)),
        (b"CTX", bytes(32)),
        (b"SUP", bytes(32)),
        (b"BAL", sections["balances_section"]),
        (b"POL", sections["pools_section"]),
        (b"LPS", sections["lp_section"]),
        (b"NNC", sections["nonce_section"]),
        (b"FEE", sections["fee_section"]),
    ):
        expected += label + encode_bytes(payload)

    assert observed == bytes(expected)


def _context_source(
    *,
    fee_policy: bool = True,
    protocol_fee_share_bps: int = 0,
    allow_snapshot_bound_quote_bindings: bool = False,
) -> FCISStepExecutionContextSourceV1:
    return FCISStepExecutionContextSourceV1(
        settlement=FCISSettlementExecutionContextSourceV1(
            now=700,
            min_lp_position_age_seconds=0,
            mode=FCISSettlementModeV1.STRONG_REPLAY,
            allow_cow_netting=False,
            allow_snapshot_bound_quote_bindings=allow_snapshot_bound_quote_bindings,
            protocol_fee_share_bps=protocol_fee_share_bps,
            protocol_fee_recipient_pubkey=(PROTOCOL if protocol_fee_share_bps > 0 else None),
        ),
        require_all_nonces=True,
        reject_settlements_with_rejected_intents=True,
        fee_split_policy=(FCISFeeSplitPolicySourceV1(3_333, 3_333, 3_334) if fee_policy else None),
        lp_duration_policy=LPDurationPolicyAdmissionSourceV1(
            base_age_seconds=0,
            max_age_seconds=3_600,
            churn_window_seconds=600,
            decay_seconds=900,
            multiplier=2,
            max_churn_tier=5,
        ),
        snapshot_version=4,
    )


def _exact_context(
    *,
    fee_policy: bool = True,
    protocol_fee_share_bps: int = 0,
    allow_snapshot_bound_quote_bindings: bool = False,
) -> FCISStepExecutionContextV1:
    result = admit_fcis_step_execution_context_v1(
        _context_source(
            fee_policy=fee_policy,
            protocol_fee_share_bps=protocol_fee_share_bps,
            allow_snapshot_bound_quote_bindings=allow_snapshot_bound_quote_bindings,
        )
    )
    assert type(result) is AdmitOk
    assert type(result.value) is FCISStepExecutionContextV1
    return result.value


def _state_source(state: DexState) -> FCISCommittedStateSourceV1:
    return FCISCommittedStateSourceV1(
        balances=admit_legacy_balance_for_differential_v1(state.balances),
        pools=admit_legacy_pool_map_for_differential_v1(state.pools),
        lp_balances=admit_legacy_lp_for_differential_v1(state.lp_balances),
        nonces=admit_legacy_nonce_for_differential_v1(state.nonces),
        vault=snapshot_vault(state.vault),
        oracle=snapshot_oracle(state.oracle),
        fee_accumulator=snapshot_fee_accumulator(state.fee_accumulator),
        perps=snapshot_perps(state.perps),
    )


def _pool_fixture(*, fee_bps: int = 30) -> tuple[str, PoolState, int]:
    return create_pool(
        asset0=ASSET0,
        asset1=ASSET1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=fee_bps,
        creator_pubkey=SENDER,
        created_at=0,
    )


def _lp_fixture(pool_id: str, pool: PoolState, owner_amount: int) -> LPTable:
    lp = LPTable()
    lp.set(SENDER, pool_id, owner_amount)
    lp.set_last_mint_timestamp(SENDER, pool_id, 0)
    locked = pool.lp_supply - owner_amount
    if locked > 0:
        lp.set("0x" + "00" * 48, pool_id, locked)
    return lp


def _single_intent_case(kind: IntentKind) -> tuple[DexState, Intent, Settlement]:
    balances = BalanceTable()
    balances.set(SENDER, ASSET0, 10_000_000)
    balances.set(SENDER, ASSET1, 10_000_000)
    if kind is IntentKind.CREATE_POOL:
        state = DexState(balances=balances, pools={}, lp_balances=LPTable())
        fields: dict[str, object] = {
            "asset0": ASSET0,
            "asset1": ASSET1,
            "fee_bps": 30,
            "amount0": 2_000_000,
            "amount1": 2_000_000,
            "nonce": 1,
        }
    else:
        pool_id, pool, owner_lp = _pool_fixture()
        state = DexState(
            balances=balances,
            pools={pool_id: pool},
            lp_balances=_lp_fixture(pool_id, pool, owner_lp),
        )
        common: dict[str, object] = {"pool_id": pool_id, "recipient": RECIPIENT, "nonce": 1}
        if kind is IntentKind.ADD_LIQUIDITY:
            fields = {
                **common,
                "amount0_desired": 100_000,
                "amount1_desired": 100_000,
                "amount0_min": 0,
                "amount1_min": 0,
            }
        elif kind is IntentKind.REMOVE_LIQUIDITY:
            fields = {**common, "lp_amount": 1_000, "amount0_min": 0, "amount1_min": 0}
        elif kind is IntentKind.SWAP_EXACT_IN:
            fields = {
                **common,
                "asset_in": ASSET0,
                "asset_out": ASSET1,
                "amount_in": 100_000,
                "min_amount_out": 1,
            }
        elif kind is IntentKind.SWAP_EXACT_OUT:
            fields = {
                **common,
                "asset_in": ASSET0,
                "asset_out": ASSET1,
                "amount_out": 10_000,
                "max_amount_in": 100_000,
            }
        else:
            raise AssertionError("route cases use their dedicated fixture")
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=kind,
        intent_id=_iid(tuple(IntentKind).index(kind) + 1),
        sender_pubkey=SENDER,
        deadline=10_000,
        fields=fields,
    )
    settlement = compute_settlement(
        [intent], state.pools, state.balances, state.lp_balances, swap_ordering="greedy_ab_refined"
    )
    assert settlement.fills[0].action is FillAction.FILL
    return state, intent, settlement


def _route_case(kind: IntentKind) -> tuple[DexState, Intent, Settlement]:
    assert kind in (IntentKind.ROUTE_EXACT_IN, IntentKind.ROUTE_EXACT_OUT)
    pool_a_id, pool_a, _ = _pool_fixture(fee_bps=30)
    pool_b_id, pool_b, _ = _pool_fixture(fee_bps=31)
    pools = {pool_a_id: pool_a, pool_b_id: pool_b}
    if kind is IntentKind.ROUTE_EXACT_IN:
        quote = best_route_exact_in_2hop(
            pools_by_id=pools, asset_in=ASSET0, asset_out=ASSET1, amount_in=100_000
        )
        receipt_kind = "exact_in"
    else:
        quote = best_route_exact_out_2hop(
            pools_by_id=pools, asset_in=ASSET0, asset_out=ASSET1, amount_out=50_000
        )
        receipt_kind = "exact_out"
    assert quote is not None
    assert all(len(leg.hops) == 1 for leg in quote.legs)
    receipt = make_route_quote_receipt(kind=receipt_kind, quote=quote, pools_by_id=pools)
    intent = create_route_intent_from_quote_receipt(
        receipt=receipt,
        pools_by_id=pools,
        sender_pubkey=SENDER,
        deadline=10_000,
        slippage_bps=0,
        nonce=1,
        recipient=RECIPIENT,
    )
    binding, error = resolve_route_binding_from_receipt(receipt)
    assert binding is not None, error
    balances = BalanceTable()
    balances.set(SENDER, ASSET0, 10_000_000)
    state = DexState(balances=balances, pools=pools, lp_balances=LPTable())
    settlement = compute_settlement(
        [intent], pools, balances, LPTable(), route_bindings={intent.intent_id: binding}
    )
    assert settlement.fills[0].action is FillAction.FILL
    fields = dict(intent.fields or {})
    fields.pop("quote_receipt_hash", None)
    fields.update(route_binding_to_fields(binding))
    sanitized = Intent(
        module=intent.module,
        version=intent.version,
        kind=intent.kind,
        intent_id=intent.intent_id,
        sender_pubkey=intent.sender_pubkey,
        deadline=intent.deadline,
        salt=intent.salt,
        fields=fields,
    )
    return state, sanitized, settlement


def _evaluate_case(
    state: DexState, intent: Intent, settlement: Settlement, *, route: bool = False
) -> FCISStepEvaluationOkV1:
    result = evaluate_fcis_step_candidate_v1(
        state_source=_state_source(state),
        settlement=snapshot_settlement(settlement),
        intents=admit_intent_batch([intent]),
        context=_context_source(allow_snapshot_bound_quote_bindings=route),
    )
    assert type(result) is FCISStepEvaluationOkV1
    return result


def test_insufficient_balance_rejection_checks_private_leaf_read(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    state, intent, settlement = _single_intent_case(IntentKind.SWAP_EXACT_IN)
    empty_state = replace(state, balances=BalanceTable())
    observed: dict[str, FCISStateReadTraceV5] = {}
    original = fcis_step_evaluator._compute_fcis_support_root_v5_admitted

    def capture_trace(**kwargs: object):
        trace = kwargs["state_read_trace"]
        assert type(trace) is FCISStateReadTraceV5
        observed["trace"] = trace
        return original(**kwargs)

    monkeypatch.setattr(
        fcis_step_evaluator,
        "_compute_fcis_support_root_v5_admitted",
        capture_trace,
    )

    result = evaluate_fcis_step_candidate_v1(
        state_source=_state_source(empty_state),
        settlement=snapshot_settlement(settlement),
        intents=admit_intent_batch([intent]),
        context=_context_source(),
    )

    assert type(result) is FCISStepEvaluationRejectV1
    assert result.phase is FCISStepEvaluationPhaseV1.SETTLEMENT
    assert (SENDER, ASSET0) in observed["trace"].balance_keys
    assert not hasattr(result, "state_read_trace")
    assert not hasattr(result, "support_evidence")
    assert not hasattr(result, "candidate")


def test_insufficient_lp_rejection_checks_private_leaf_read(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    state, intent, settlement = _single_intent_case(IntentKind.REMOVE_LIQUIDITY)
    empty_state = replace(state, lp_balances=LPTable())
    pool_id = cast(str, intent.fields["pool_id"])
    observed: dict[str, FCISStateReadTraceV5] = {}
    original = fcis_step_evaluator._compute_fcis_support_root_v5_admitted

    def capture_trace(**kwargs: object):
        trace = kwargs["state_read_trace"]
        assert type(trace) is FCISStateReadTraceV5
        observed["trace"] = trace
        return original(**kwargs)

    monkeypatch.setattr(
        fcis_step_evaluator,
        "_compute_fcis_support_root_v5_admitted",
        capture_trace,
    )

    result = evaluate_fcis_step_candidate_v1(
        state_source=_state_source(empty_state),
        settlement=snapshot_settlement(settlement),
        intents=admit_intent_batch([intent]),
        context=_context_source(),
    )

    assert type(result) is FCISStepEvaluationRejectV1
    assert result.phase is FCISStepEvaluationPhaseV1.SETTLEMENT
    assert (SENDER, pool_id) in observed["trace"].lp_keys
    assert not hasattr(result, "state_read_trace")
    assert not hasattr(result, "support_evidence")
    assert not hasattr(result, "candidate")


def _rejected_settlement(intents: tuple[OwnedIntentV1, ...]):
    return snapshot_settlement(
        Settlement(
            module="TauSwap",
            version="0.1",
            batch_ref="support-v5-unit",
            included_intents=[(intent.intent_id, FillAction.REJECT) for intent in intents],
            fills=[],
            balance_deltas=[],
            reserve_deltas=[],
            lp_deltas=[],
            events=None,
        )
    )


def _direct_evidence(
    *,
    intents: tuple[OwnedIntentV1, ...],
    context: FCISStepExecutionContextV1,
    balances: BalanceTable,
    pools: dict[str, PoolState],
    lp: LPTable | None = None,
    nonces: NonceTable | None = None,
    fee: FeeAccumulatorState | None = None,
    trace: FCISStateReadTraceV5 | None = None,
) -> FCISSupportRootEvidenceV5:
    return compute_fcis_support_root_v5(
        settlement=_rejected_settlement(intents),
        intents=intents,
        context=context,
        balances=admit_legacy_balance_for_differential_v1(balances),
        pools=admit_legacy_pool_map_for_differential_v1(pools),
        lp_balances=admit_legacy_lp_for_differential_v1(lp or LPTable()),
        nonces=admit_legacy_nonce_for_differential_v1(nonces or NonceTable()),
        fee_accumulator=snapshot_fee_accumulator(fee or FeeAccumulatorState()),
        state_read_trace=trace or FCISStateReadTraceV5(),
        context_read_trace=read_step_execution_context_v5(context)[1],
    )


def _owned_direct_intents(pool_ids: tuple[str, str]) -> dict[IntentKind, OwnedIntentV1]:
    pool_a, pool_b = pool_ids
    base: dict[IntentKind, dict[str, object]] = {
        IntentKind.CREATE_POOL: {
            "asset0": ASSET0,
            "asset1": ASSET1,
            "fee_bps": 29,
            "amount0": 100,
            "amount1": 200,
            "nonce": 1,
        },
        IntentKind.ADD_LIQUIDITY: {
            "pool_id": pool_a,
            "recipient": RECIPIENT,
            "amount0_desired": 10,
            "amount1_desired": 20,
            "amount0_min": 0,
            "amount1_min": 0,
            "nonce": 1,
        },
        IntentKind.REMOVE_LIQUIDITY: {
            "pool_id": pool_a,
            "recipient": RECIPIENT,
            "lp_amount": 1,
            "amount0_min": 0,
            "amount1_min": 0,
            "nonce": 1,
        },
        IntentKind.SWAP_EXACT_IN: {
            "pool_id": pool_a,
            "asset_in": ASSET0,
            "asset_out": ASSET1,
            "recipient": RECIPIENT,
            "amount_in": 10,
            "min_amount_out": 1,
            "nonce": 1,
        },
        IntentKind.SWAP_EXACT_OUT: {
            "pool_id": pool_a,
            "asset_in": ASSET0,
            "asset_out": ASSET1,
            "recipient": RECIPIENT,
            "amount_out": 1,
            "max_amount_in": 10,
            "nonce": 1,
        },
    }
    route_common: dict[str, object] = {
        "asset_in": ASSET0,
        "asset_out": ASSET1,
        "recipient": RECIPIENT,
        "leg_indices": [0, 1],
        "route_legs": [
            {
                "pool_id": pool_a,
                "asset_in": ASSET0,
                "asset_out": ASSET1,
                "amount_in": 4,
                "amount_out": 3,
            },
            {
                "pool_id": pool_b,
                "asset_in": ASSET0,
                "asset_out": ASSET1,
                "amount_in": 6,
                "amount_out": 5,
            },
        ],
        "route_pool_fingerprints": {pool_a: "0x" + "aa" * 32, pool_b: "0x" + "bb" * 32},
        "nonce": 1,
    }
    base[IntentKind.ROUTE_EXACT_IN] = {
        **route_common,
        "total_amount_in": 10,
        "total_min_amount_out": 1,
    }
    base[IntentKind.ROUTE_EXACT_OUT] = {
        **route_common,
        "total_amount_out": 8,
        "total_max_amount_in": 10,
    }
    return {
        kind: admit_intent_batch(
            [
                Intent(
                    module="TauSwap",
                    version="0.1",
                    kind=kind,
                    intent_id=_iid(100 + index),
                    sender_pubkey=SENDER,
                    deadline=10_000,
                    fields=base[kind],
                )
            ]
        )[0]
        for index, kind in enumerate(IntentKind, start=1)
    }


def test_v5_profile_is_complete_and_source_inventories_are_exhaustive() -> None:
    assert FCIS_SUPPORT_PROFILE_COMPLETE_V5 is True
    assert FCIS_SUPPORT_PROFILE_VERSION_V5 == 5
    assert FCIS_SUPPORT_PROFILE_ID_V5 == "zenodex/fcis/support-profile/v5"
    assert tuple(kind for kind, _fields in FCIS_SUPPORT_INTENT_FIELD_INVENTORY_V5) == tuple(
        kind.value for kind in IntentKind
    )
    assert tuple(kind for kind, _fields in FCIS_SUPPORT_FIELD_DEPENDENCIES_V5) == tuple(
        kind.value for kind in IntentKind
    )
    dependencies = dict(FCIS_SUPPORT_FIELD_DEPENDENCIES_V5)
    command_only = dict(FCIS_SUPPORT_COMMAND_ONLY_FIELDS_V5)
    for kind_text, fields in FCIS_SUPPORT_INTENT_FIELD_INVENTORY_V5:
        kind = next(item for item in IntentKind if item.value == kind_text)
        assert fields == intent_allowed_field_names_v1(kind)
        assert not set(dependencies[kind_text]) & set(command_only[kind_text])
        assert set(dependencies[kind_text]) | set(command_only[kind_text]) == set(fields)
    expected_context = tuple(
        sorted(
            tuple(f"settlement.{name}" for name in FCIS_SETTLEMENT_CONTEXT_FIELD_NAMES_V1)
            + (
                "require_all_nonces",
                "reject_settlements_with_rejected_intents",
                "snapshot_version",
                "fee_split_policy",
                "lp_duration_policy",
            )
            + tuple(f"fee_split_policy.{name}" for name in FCIS_FEE_SPLIT_POLICY_FIELD_NAMES_V1)
            + tuple(f"lp_duration_policy.{name}" for name in FCIS_LP_DURATION_POLICY_FIELD_NAMES_V1)
        )
    )
    assert FCIS_SUPPORT_CONTEXT_PATHS_V5 == expected_context
    assert FCIS_CONTEXT_SCHEMA_PATHS_V5 == expected_context
    assert tuple(kind for kind, _fields in FCIS_SUPPORT_COMMAND_ONLY_FIELDS_V5) == tuple(
        kind.value for kind in IntentKind
    )


def test_v5_context_projection_reads_the_complete_closed_schema() -> None:
    context = _exact_context()

    projection, trace = read_step_execution_context_v5(context)

    assert trace.paths == FCIS_CONTEXT_SCHEMA_PATHS_V5
    assert projection.now == context.settlement.now
    assert projection.fee_split_policy == context.fee_split_policy
    assert projection.lp_duration_policy == context.lp_duration_policy
    assert projection.snapshot_version == context.snapshot_version


def test_v5_inventory_rejects_an_unclassified_source_field(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    inventory = tuple(
        (
            kind,
            fields
            + (("future_authority_field",) if kind == IntentKind.SWAP_EXACT_IN.value else ()),
        )
        for kind, fields in FCIS_SUPPORT_INTENT_FIELD_INVENTORY_V5
    )
    monkeypatch.setattr(
        fcis_support_profile_v5,
        "FCIS_SUPPORT_INTENT_FIELD_INVENTORY_V5",
        inventory,
    )

    with pytest.raises(RuntimeError, match="classification is incomplete"):
        fcis_support_profile_v5._validate_support_field_inventory_v5()


@pytest.mark.parametrize(
    "kind",
    (
        IntentKind.CREATE_POOL,
        IntentKind.ADD_LIQUIDITY,
        IntentKind.REMOVE_LIQUIDITY,
        IntentKind.SWAP_EXACT_IN,
        IntentKind.SWAP_EXACT_OUT,
    ),
)
def test_exact_evaluator_proves_observed_reads_are_contained(kind: IntentKind) -> None:
    result = _evaluate_case(*_single_intent_case(kind))
    assert result.evidence.support_root_version == 5
    assert result.evidence.support_profile_id == FCIS_SUPPORT_PROFILE_ID_V5


@pytest.mark.parametrize("kind", (IntentKind.ROUTE_EXACT_IN, IntentKind.ROUTE_EXACT_OUT))
def test_exact_route_evaluator_proves_every_leg_read_is_contained(kind: IntentKind) -> None:
    state, intent, settlement = _route_case(kind)
    result = _evaluate_case(state, intent, settlement, route=True)
    support = derive_fcis_support_set_v5(
        intents=result.material.intents,
        pools=result.material.pre_state.pools,
        context=result.material.context,
    )
    assert set(support.pool_ids) == set(state.pools)
    assert result.evidence.support_root_version == 5


def test_support_set_covers_recipient_protocol_fee_and_all_intent_kinds() -> None:
    pool_a_id, pool_a, _ = _pool_fixture(fee_bps=30)
    pool_b_id, pool_b, _ = _pool_fixture(fee_bps=31)
    intents = _owned_direct_intents((pool_a_id, pool_b_id))
    context = _exact_context(protocol_fee_share_bps=1_000)
    pools = admit_legacy_pool_map_for_differential_v1({pool_a_id: pool_a, pool_b_id: pool_b})
    create = derive_fcis_support_set_v5(
        intents=(intents[IntentKind.CREATE_POOL],), pools=pools, context=context
    )
    assert {(SENDER, ASSET0), (SENDER, ASSET1)} <= set(create.balance_keys)
    assert len(create.lp_keys) == 2
    add = derive_fcis_support_set_v5(
        intents=(intents[IntentKind.ADD_LIQUIDITY],), pools=pools, context=context
    )
    assert {(SENDER, ASSET0), (SENDER, ASSET1)} <= set(add.balance_keys)
    assert add.lp_keys == ((RECIPIENT, pool_a_id),)
    remove = derive_fcis_support_set_v5(
        intents=(intents[IntentKind.REMOVE_LIQUIDITY],), pools=pools, context=context
    )
    assert {(RECIPIENT, ASSET0), (RECIPIENT, ASSET1)} <= set(remove.balance_keys)
    assert remove.lp_keys == ((SENDER, pool_a_id),)
    for kind in (IntentKind.SWAP_EXACT_IN, IntentKind.SWAP_EXACT_OUT):
        swap = derive_fcis_support_set_v5(intents=(intents[kind],), pools=pools, context=context)
        assert {(SENDER, ASSET0), (RECIPIENT, ASSET1), (PROTOCOL, ASSET0)} <= set(swap.balance_keys)
        assert swap.pool_ids == (pool_a_id,)
    for kind in (IntentKind.ROUTE_EXACT_IN, IntentKind.ROUTE_EXACT_OUT):
        route = derive_fcis_support_set_v5(intents=(intents[kind],), pools=pools, context=context)
        assert {(SENDER, ASSET0), (RECIPIENT, ASSET1), (PROTOCOL, ASSET0)} <= set(
            route.balance_keys
        )
        assert route.pool_ids == tuple(sorted((pool_a_id, pool_b_id)))
        assert route.include_fee_accumulator is True


def test_create_then_add_derives_absent_pool_assets_before_evaluation() -> None:
    pool_id, _pool, _ = _pool_fixture(fee_bps=29)
    intents = _owned_direct_intents((pool_id, _pool_fixture(fee_bps=31)[0]))
    support = derive_fcis_support_set_v5(
        intents=(intents[IntentKind.CREATE_POOL], intents[IntentKind.ADD_LIQUIDITY]),
        pools=admit_legacy_pool_map_for_differential_v1({}),
        context=_exact_context(),
    )
    assert {(SENDER, ASSET0), (SENDER, ASSET1)} <= set(support.balance_keys)
    assert (RECIPIENT, pool_id) in support.lp_keys


def test_undeclared_observed_read_fails_closed() -> None:
    pool_id, pool, _ = _pool_fixture()
    intent = _owned_direct_intents((pool_id, _pool_fixture(fee_bps=31)[0]))[
        IntentKind.SWAP_EXACT_IN
    ]
    balances = BalanceTable()
    balances.set(SENDER, ASSET0, 1_000)
    with pytest.raises(ValueError, match="escaped declared support"):
        _direct_evidence(
            intents=(intent,),
            context=_exact_context(),
            balances=balances,
            pools={pool_id: pool},
            trace=FCISStateReadTraceV5(balance_keys=((OTHER, OTHER_ASSET),)),
        )


def test_public_support_root_rejects_trace_lookalike_before_attribute_access() -> None:
    pool_id, pool, _ = _pool_fixture()
    intent = _owned_direct_intents((pool_id, _pool_fixture(fee_bps=31)[0]))[
        IntentKind.SWAP_EXACT_IN
    ]
    balances = BalanceTable()
    balances.set(SENDER, ASSET0, 1_000)
    with pytest.raises(TypeError, match="exact state-read trace"):
        compute_fcis_support_root_v5(
            settlement=_rejected_settlement((intent,)),
            intents=(intent,),
            context=_exact_context(),
            balances=admit_legacy_balance_for_differential_v1(balances),
            pools=admit_legacy_pool_map_for_differential_v1({pool_id: pool}),
            lp_balances=admit_legacy_lp_for_differential_v1(LPTable()),
            nonces=admit_legacy_nonce_for_differential_v1(NonceTable()),
            fee_accumulator=snapshot_fee_accumulator(FeeAccumulatorState()),
            state_read_trace=cast(FCISStateReadTraceV5, object()),
            context_read_trace=read_step_execution_context_v5(_exact_context())[1],
        )


def test_presence_tags_distinguish_absent_pool_and_absent_nonce_from_present_zero() -> None:
    pool_id, pool, _ = _pool_fixture()
    intent = _owned_direct_intents((pool_id, _pool_fixture(fee_bps=31)[0]))[
        IntentKind.SWAP_EXACT_IN
    ]
    balances = BalanceTable()
    balances.set(SENDER, ASSET0, 1_000)
    absent = _direct_evidence(
        intents=(intent,), context=_exact_context(), balances=balances, pools={}
    )
    present_pool = _direct_evidence(
        intents=(intent,), context=_exact_context(), balances=balances, pools={pool_id: pool}
    )
    zero_nonce = NonceTable()
    zero_nonce.set_last(SENDER, 0)
    present_zero = _direct_evidence(
        intents=(intent,), context=_exact_context(), balances=balances, pools={}, nonces=zero_nonce
    )
    assert len({absent.root, present_pool.root, present_zero.root}) == 3


def test_support_keys_are_committed_even_when_both_values_are_absent() -> None:
    pool_a_id, _pool_a, _ = _pool_fixture(fee_bps=30)
    pool_b_id, _pool_b, _ = _pool_fixture(fee_bps=31)
    intents = _owned_direct_intents((pool_a_id, pool_b_id))
    support_a = derive_fcis_support_set_v5(
        intents=(intents[IntentKind.SWAP_EXACT_IN],),
        pools=admit_legacy_pool_map_for_differential_v1({}),
        context=_exact_context(),
    )
    changed = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(999),
        sender_pubkey=OTHER,
        deadline=10_000,
        fields={
            "pool_id": pool_a_id,
            "asset_in": OTHER_ASSET,
            "asset_out": ASSET1,
            "amount_in": 1,
            "min_amount_out": 1,
            "nonce": 1,
        },
    )
    support_b = derive_fcis_support_set_v5(
        intents=admit_intent_batch([changed]),
        pools=admit_legacy_pool_map_for_differential_v1({}),
        context=_exact_context(),
    )
    assert support_a.balance_keys != support_b.balance_keys
    assert support_a != support_b


def test_irrelevant_state_cells_do_not_change_the_support_root() -> None:
    pool_id, pool, _ = _pool_fixture()
    other_pool_id, other_pool, _ = create_pool(
        asset0=ASSET0,
        asset1=OTHER_ASSET,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=32,
        creator_pubkey=OTHER,
    )
    intent = _owned_direct_intents((pool_id, _pool_fixture(fee_bps=31)[0]))[
        IntentKind.SWAP_EXACT_IN
    ]
    balances = BalanceTable()
    balances.set(SENDER, ASSET0, 1_000)
    base = _direct_evidence(
        intents=(intent,), context=_exact_context(), balances=balances, pools={pool_id: pool}
    )
    balances.set(OTHER, OTHER_ASSET, 999)
    lp = LPTable()
    lp.set(OTHER, other_pool_id, 7)
    nonces = NonceTable()
    nonces.set_last(OTHER, 9)
    changed = _direct_evidence(
        intents=(intent,),
        context=_exact_context(),
        balances=balances,
        pools={pool_id: pool, other_pool_id: other_pool},
        lp=lp,
        nonces=nonces,
    )
    assert changed.root == base.root
    assert changed.root_preimage == base.root_preimage


def test_every_lp_position_component_is_committed() -> None:
    pool_id, pool, owner_lp = _pool_fixture()
    intent = _owned_direct_intents((pool_id, _pool_fixture(fee_bps=31)[0]))[
        IntentKind.REMOVE_LIQUIDITY
    ]
    balances = BalanceTable()
    context = _exact_context()

    def root(
        *,
        amount: int = owner_lp,
        mint: int = 10,
        remove: int = 20,
        churn: int = 2,
        churn_update: int = 30,
    ) -> str:
        lp = LPTable()
        lp.set(SENDER, pool_id, amount)
        lp.set_last_mint_timestamp(SENDER, pool_id, mint)
        lp.set_last_remove_timestamp(SENDER, pool_id, remove)
        lp.set_churn_tier(SENDER, pool_id, churn)
        lp.set_last_churn_update_timestamp(SENDER, pool_id, churn_update)
        return _direct_evidence(
            intents=(intent,), context=context, balances=balances, pools={pool_id: pool}, lp=lp
        ).root

    assert (
        len(
            {
                root(),
                root(amount=owner_lp + 1),
                root(mint=11),
                root(remove=21),
                root(churn=3),
                root(churn_update=31),
            }
        )
        == 6
    )


def test_declared_balance_pool_nonce_and_fee_changes_each_change_root() -> None:
    pool_id, pool, _ = _pool_fixture()
    intent = _owned_direct_intents((pool_id, _pool_fixture(fee_bps=31)[0]))[
        IntentKind.SWAP_EXACT_IN
    ]
    context = _exact_context()

    def root(
        *,
        amount: int = 1_000,
        pool_value: PoolState = pool,
        nonce: int | None = None,
        dust: int = 0,
    ) -> str:
        balances = BalanceTable()
        balances.set(SENDER, ASSET0, amount)
        nonces = NonceTable()
        if nonce is not None:
            nonces.set_last(SENDER, nonce)
        return _direct_evidence(
            intents=(intent,),
            context=context,
            balances=balances,
            pools={pool_id: pool_value},
            nonces=nonces,
            fee=FeeAccumulatorState(dust),
        ).root

    assert (
        len(
            {
                root(),
                root(amount=1_001),
                root(pool_value=replace(pool, reserve0=pool.reserve0 + 1)),
                root(nonce=1),
                root(dust=1),
            }
        )
        == 5
    )


def test_every_context_field_is_bound_by_the_context_hash() -> None:
    pool_id, pool, _ = _pool_fixture()
    intent = _owned_direct_intents((pool_id, _pool_fixture(fee_bps=31)[0]))[
        IntentKind.SWAP_EXACT_IN
    ]
    balances = BalanceTable()
    balances.set(SENDER, ASSET0, 1_000)
    base = _exact_context(protocol_fee_share_bps=1_000)
    assert base.fee_split_policy is not None
    assert base.lp_duration_policy is not None
    fee = base.fee_split_policy
    lp = base.lp_duration_policy
    variants = (
        replace(base, settlement=replace(base.settlement, now=701)),
        replace(base, settlement=replace(base.settlement, min_lp_position_age_seconds=1)),
        replace(base, settlement=replace(base.settlement, allow_cow_netting=True)),
        replace(
            base, settlement=replace(base.settlement, allow_snapshot_bound_quote_bindings=True)
        ),
        replace(base, settlement=replace(base.settlement, protocol_fee_share_bps=999)),
        replace(base, settlement=replace(base.settlement, protocol_fee_recipient_pubkey=OTHER)),
        replace(base, fee_split_policy=replace(fee, buyback_bps=3_332, rewards_bps=3_335)),
        replace(base, fee_split_policy=replace(fee, treasury_bps=3_332, rewards_bps=3_335)),
        replace(base, fee_split_policy=None),
        replace(base, lp_duration_policy=replace(lp, base_age_seconds=1)),
        replace(base, lp_duration_policy=replace(lp, max_age_seconds=3_601)),
        replace(base, lp_duration_policy=replace(lp, churn_window_seconds=601)),
        replace(base, lp_duration_policy=replace(lp, decay_seconds=901)),
        replace(base, lp_duration_policy=replace(lp, multiplier=3)),
        replace(base, lp_duration_policy=replace(lp, max_churn_tier=6)),
        replace(base, lp_duration_policy=None),
        replace(base, require_all_nonces=False),
        replace(base, reject_settlements_with_rejected_intents=False),
        replace(base, snapshot_version=3),
    )
    base_hash = _direct_evidence(
        intents=(intent,), context=base, balances=balances, pools={pool_id: pool}
    ).execution_context_hash
    for variant in variants:
        assert (
            _direct_evidence(
                intents=(intent,), context=variant, balances=balances, pools={pool_id: pool}
            ).execution_context_hash
            != base_hash
        )


def test_evaluator_support_root_uses_pre_state_not_successor(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    state, intent, settlement = _single_intent_case(IntentKind.SWAP_EXACT_IN)
    observed: dict[str, object] = {}
    original = fcis_step_evaluator._compute_fcis_support_root_v5_admitted

    def spy(**kwargs: object) -> FCISSupportRootEvidenceV5:
        observed.update(kwargs)
        typed_original = cast(Callable[..., FCISSupportRootEvidenceV5], original)
        return typed_original(**kwargs)

    monkeypatch.setattr(fcis_step_evaluator, "_compute_fcis_support_root_v5_admitted", spy)
    result = _evaluate_case(state, intent, settlement)
    assert observed["balances"] == result.material.pre_state.balances
    assert observed["pools"] == result.material.pre_state.pools
    assert observed["lp_balances"] == result.material.pre_state.lp_balances
    assert observed["nonces"] == result.material.pre_state.nonces
    assert observed["fee_accumulator"] == result.material.pre_state.fee_accumulator
    assert observed["balances"] != result.candidate.state.balances
    assert observed["pools"] != result.candidate.state.pools


def test_v4_and_incomplete_prototype_remain_pinned_while_complete_v5_is_unmounted() -> None:
    from src.core.fcis_step_evaluator import FCIS_STEP_EVALUATOR_UNMOUNTED_V1
    from src.state.support_root import (
        EXACT_SUPPORT_ROOT_VERSION_V1,
        INCOMPLETE_SUPPORT_ROOT_PROTOTYPE_VERSION_V1,
        SUPPORT_ROOT_VERSION,
    )

    assert SUPPORT_ROOT_VERSION == 4
    assert INCOMPLETE_SUPPORT_ROOT_PROTOTYPE_VERSION_V1 == 5
    assert EXACT_SUPPORT_ROOT_VERSION_V1 == INCOMPLETE_SUPPORT_ROOT_PROTOTYPE_VERSION_V1
    assert FCIS_SUPPORT_PROFILE_VERSION_V5 == 5
    assert FCIS_STEP_EVALUATOR_UNMOUNTED_V1 is True


@settings(max_examples=40, deadline=None, derandomize=True)
@given(
    extra_balance=st.integers(min_value=0, max_value=1_000_000),
    extra_lp=st.integers(min_value=0, max_value=1_000_000),
    extra_nonce=st.integers(min_value=0, max_value=1_000_000),
)
def test_property_irrelevant_state_cells_preserve_support_root(
    extra_balance: int,
    extra_lp: int,
    extra_nonce: int,
) -> None:
    pool_id, pool, _ = _pool_fixture()
    other_pool_id, _other_pool, _ = create_pool(
        asset0=ASSET0,
        asset1=OTHER_ASSET,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=32,
        creator_pubkey=OTHER,
        created_at=0,
    )
    intent = _owned_direct_intents((pool_id, _pool_fixture(fee_bps=31)[0]))[
        IntentKind.SWAP_EXACT_IN
    ]
    base_balances = BalanceTable()
    base_balances.set(SENDER, ASSET0, 1_000)
    base = _direct_evidence(
        intents=(intent,),
        context=_exact_context(),
        balances=base_balances,
        pools={pool_id: pool},
    )

    changed_balances = BalanceTable()
    changed_balances.set(SENDER, ASSET0, 1_000)
    changed_balances.set(OTHER, OTHER_ASSET, extra_balance)
    changed_lp = LPTable()
    changed_lp.set(OTHER, other_pool_id, extra_lp)
    changed_nonces = NonceTable()
    changed_nonces.set_last(OTHER, extra_nonce)
    changed = _direct_evidence(
        intents=(intent,),
        context=_exact_context(),
        balances=changed_balances,
        pools={pool_id: pool},
        lp=changed_lp,
        nonces=changed_nonces,
    )

    assert changed.root_preimage == base.root_preimage
    assert changed.root == base.root


@settings(max_examples=40, deadline=None, derandomize=True)
@given(
    amount=st.integers(min_value=0, max_value=1_000_000),
    nonce=st.integers(min_value=0, max_value=1_000_000),
    dust=st.integers(min_value=0, max_value=1_000_000),
    delta=st.integers(min_value=1, max_value=1_000),
)
def test_property_each_declared_state_cell_changes_support_root(
    amount: int,
    nonce: int,
    dust: int,
    delta: int,
) -> None:
    pool_id, pool, _ = _pool_fixture()
    intent = _owned_direct_intents((pool_id, _pool_fixture(fee_bps=31)[0]))[
        IntentKind.SWAP_EXACT_IN
    ]
    context = _exact_context()

    def root(
        *,
        balance_value: int = amount,
        nonce_value: int = nonce,
        dust_value: int = dust,
        reserve_delta: int = 0,
    ) -> str:
        balances = BalanceTable()
        balances.set(SENDER, ASSET0, balance_value)
        nonces = NonceTable()
        nonces.set_last(SENDER, nonce_value)
        return _direct_evidence(
            intents=(intent,),
            context=context,
            balances=balances,
            pools={pool_id: replace(pool, reserve0=pool.reserve0 + reserve_delta)},
            nonces=nonces,
            fee=FeeAccumulatorState(dust_value),
        ).root

    baseline = root()
    assert root(balance_value=amount + delta) != baseline
    assert root(nonce_value=nonce + delta) != baseline
    assert root(dust_value=dust + delta) != baseline
    assert root(reserve_delta=delta) != baseline


@settings(max_examples=40, deadline=None, derandomize=True)
@given(
    amount=st.integers(min_value=0, max_value=1_000_000),
    nonce=st.integers(min_value=0, max_value=1_000_000),
    dust=st.integers(min_value=0, max_value=1_000_000),
)
def test_property_support_root_recomputation_is_byte_deterministic(
    amount: int,
    nonce: int,
    dust: int,
) -> None:
    pool_id, pool, _ = _pool_fixture()
    intent = _owned_direct_intents((pool_id, _pool_fixture(fee_bps=31)[0]))[
        IntentKind.SWAP_EXACT_IN
    ]

    def evidence() -> FCISSupportRootEvidenceV5:
        balances = BalanceTable()
        balances.set(SENDER, ASSET0, amount)
        nonces = NonceTable()
        nonces.set_last(SENDER, nonce)
        return _direct_evidence(
            intents=(intent,),
            context=_exact_context(),
            balances=balances,
            pools={pool_id: pool},
            nonces=nonces,
            fee=FeeAccumulatorState(dust),
        )

    first = evidence()
    second = evidence()
    assert first == second
    assert first.support_set_preimage == second.support_set_preimage
    assert first.root_preimage == second.root_preimage


@settings(max_examples=30, deadline=None, derandomize=True)
@given(
    read_kind=st.sampled_from(("balance", "pool", "lp", "nonce", "fee")),
    suffix=st.integers(min_value=0, max_value=2**32 - 1),
)
def test_property_every_undeclared_read_class_fails_closed(
    read_kind: str,
    suffix: int,
) -> None:
    pool_id, pool, _ = _pool_fixture()
    intent = _owned_direct_intents((pool_id, _pool_fixture(fee_bps=31)[0]))[
        IntentKind.SWAP_EXACT_IN
    ]
    outsider = "0x80" + f"{suffix:094x}"
    outsider_asset = "0x81" + f"{suffix:062x}"
    outsider_pool = "0x82" + f"{suffix:062x}"
    context = _exact_context()
    if read_kind == "balance":
        trace = FCISStateReadTraceV5(balance_keys=((outsider, outsider_asset),))
    elif read_kind == "pool":
        trace = FCISStateReadTraceV5(pool_ids=(outsider_pool,))
    elif read_kind == "lp":
        trace = FCISStateReadTraceV5(lp_keys=((outsider, outsider_pool),))
    elif read_kind == "nonce":
        trace = FCISStateReadTraceV5(nonce_keys=(outsider,))
    else:
        trace = FCISStateReadTraceV5(reads_fee_accumulator=True)
        context = _exact_context(fee_policy=False)

    with pytest.raises(ValueError, match="escaped declared support"):
        _direct_evidence(
            intents=(intent,),
            context=context,
            balances=BalanceTable(),
            pools={pool_id: pool},
            trace=trace,
        )


def test_unrelated_full_state_fields_do_not_enter_the_local_support_projection() -> None:
    pool_id, _pool, _ = _pool_fixture()
    state, intent, settlement = _single_intent_case(IntentKind.SWAP_EXACT_IN)
    first = _evaluate_case(state, intent, settlement)
    changed = replace(
        _state_source(state),
        vault=snapshot_vault(VaultState(1, 0, 0, 0, 0)),
        oracle=snapshot_oracle(OracleState(123, 300)),
        perps=snapshot_perps(PerpsState(version=PERPS_STATE_VERSION_V4, markets={})),
    )
    second = evaluate_fcis_step_candidate_v1(
        state_source=changed,
        settlement=snapshot_settlement(settlement),
        intents=admit_intent_batch([intent]),
        context=_context_source(),
    )
    assert type(second) is FCISStepEvaluationOkV1
    assert first.evidence.support_root == second.evidence.support_root
    assert first.evidence.pre_state_root != second.evidence.pre_state_root
    assert pool_id in state.pools
