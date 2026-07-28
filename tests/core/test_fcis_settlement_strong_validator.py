"""Exact-only contract tests for the unmounted FCIS strong validator."""

from __future__ import annotations

from dataclasses import replace
from typing import cast

from src.core.fcis_settlement_strong_validator import (
    evaluate_settlement_strong_exact_v1,
)
from src.core.fcis_settlement_strong_values import (
    ExactSpotPreStateV1,
    ExactStrongSettlementCandidateV1,
    ExactStrongSettlementRejectV1,
    StrongSettlementContextV1,
)
from src.core.settlement_snapshots import (
    OwnedBalanceDeltaV1,
    OwnedFillV1,
    OwnedLPDeltaV1,
    OwnedReserveDeltaV1,
    OwnedSettlementV1,
    snapshot_settlement,
)
from src.state.fcis_execution_context_admission import admit as admit_context
from src.state.fcis_execution_context_values import (
    FCIS_EXECUTION_CONTEXT_SCHEMA_REVISION_V1,
    FCIS_SETTLEMENT_CONTEXT_SCHEMA_ID_V1,
    FCISSettlementExecutionContextSourceV1,
    FCISSettlementExecutionContextV1,
    FCISSettlementModeV1,
)
from src.state.fcis_pool_identity import compute_pool_id
from src.state.intent_snapshots import OwnedIntentV1, snapshot_intent
from src.state.owned_collections import (
    OwnedEnumV1,
    OwnedMapV1,
    _owned_enum_from_admitted,
    _owned_map_from_admitted,
)
from src.state.owned_json import (
    OwnedJsonValueV1,
    snapshot_owned_json_object,
)
from src.state.pool_creation_transition import (
    PoolCreationBuildOkV1,
    PoolCreationV1,
    build_committed_pool_creation_v1,
)
from src.state.snapshot_combinators import (
    AdmissionLimitsV1,
    AdmitOk,
    ValidatedAdmissionLimitsV1,
    build_admission_limits_v1,
)
from src.state.state_admission_profile import admit as admit_state
from src.state.state_snapshot_schema import (
    BALANCE_TABLE_ADMISSION_SCHEMA_ID_V1,
    LP_TABLE_ADMISSION_SCHEMA_ID_V1,
    POOL_MAP_ADMISSION_SCHEMA_ID_V1,
    StateEnumTagV1,
    state_enum_tag_ordinal_v1,
)
from src.state.state_snapshot_values import (
    FCIS_STATE_SCHEMA_REVISION_V1,
    CommittedBalanceTableV1,
    CommittedLPTableV1,
    CommittedPoolStateV1,
    _BalanceSourceV1,
    _LPSourceV1,
)

SENDER = "0x" + "11" * 48
RECIPIENT = "0x" + "22" * 48
FEE_RECIPIENT = "0x" + "99" * 48
OTHER_FEE_RECIPIENT = "0x" + "88" * 48
LP_LOCK = "0x" + "00" * 48
ASSET0 = "0x" + "01" * 32
ASSET1 = "0x" + "02" * 32
POOL_ID = compute_pool_id(ASSET0, ASSET1, 30)

SWAP_INTENT_ID = "0x" + f"{900:064x}"
CREATE_INTENT_ID = "0x" + f"{901:064x}"
EXACT_OUT_INTENT_ID = "0x" + f"{904:064x}"
ADD_LIQUIDITY_INTENT_ID = "0x" + f"{906:064x}"
REMOVE_LIQUIDITY_INTENT_ID = "0x" + f"{907:064x}"

INITIAL_RESERVE = 2_000_000
INITIAL_BALANCE = 10_000_000
INITIAL_LP_SUPPLY = 2_000_000
PROVIDER_LP = 1_999_000
MINIMUM_LP_LOCK = 1_000

SWAP_AMOUNT_IN = 1_000
SWAP_FEE = 3
SWAP_AMOUNT_OUT = 996
EXACT_OUT_AMOUNT_IN = 1_005
EXACT_OUT_AMOUNT_OUT = 1_000
EXACT_OUT_FEE = 4
LIQUIDITY_AMOUNT = 100_000
REMOVE_LP_AMOUNT = 1_000

INTENT_KIND_CREATE_POOL_ORDINAL = 0
INTENT_KIND_ADD_LIQUIDITY_ORDINAL = 1
INTENT_KIND_REMOVE_LIQUIDITY_ORDINAL = 2
INTENT_KIND_SWAP_EXACT_IN_ORDINAL = 3
INTENT_KIND_SWAP_EXACT_OUT_ORDINAL = 4
FILL_ACTION_FILL_ORDINAL = 0
FILL_ACTION_REJECT_ORDINAL = 1


def _limits() -> ValidatedAdmissionLimitsV1:
    result = build_admission_limits_v1(
        AdmissionLimitsV1(
            max_depth=64,
            max_nodes=200_000,
            max_canonical_bytes=4_000_000,
            max_collection_items=200_000,
        )
    )
    if type(result) is not ValidatedAdmissionLimitsV1:
        raise AssertionError("test admission limits must be valid")
    return result


def _state_enum(tag: StateEnumTagV1, member_ordinal: int) -> OwnedEnumV1:
    return _owned_enum_from_admitted(
        FCIS_STATE_SCHEMA_REVISION_V1,
        state_enum_tag_ordinal_v1(tag),
        member_ordinal,
    )


def _intent_fields(
    kind_name: str,
    entries: tuple[tuple[str, OwnedJsonValueV1], ...],
) -> OwnedMapV1[str, OwnedJsonValueV1]:
    return _owned_map_from_admitted(
        entries,
        FCIS_STATE_SCHEMA_REVISION_V1,
        f"zenodex/fcis/authority/intent-fields/{kind_name}/v1",
    )


def _intent(
    *,
    member_ordinal: int,
    kind_name: str,
    intent_id: str,
    fields: tuple[tuple[str, OwnedJsonValueV1], ...],
    sender_pubkey: str = SENDER,
) -> OwnedIntentV1:
    return snapshot_intent(
        OwnedIntentV1(
            module="TauSwap",
            version="0.1",
            kind=_state_enum(StateEnumTagV1.INTENT_KIND, member_ordinal),
            intent_id=intent_id,
            sender_pubkey=sender_pubkey,
            deadline=9_999_999_999,
            salt=None,
            fields=_intent_fields(kind_name, fields),
        )
    )


def _fill_action() -> OwnedEnumV1:
    return _state_enum(
        StateEnumTagV1.FILL_ACTION,
        FILL_ACTION_FILL_ORDINAL,
    )


def _reject_action() -> OwnedEnumV1:
    return _state_enum(
        StateEnumTagV1.FILL_ACTION,
        FILL_ACTION_REJECT_ORDINAL,
    )


def _balances(
    *entries: tuple[tuple[str, str], int],
) -> CommittedBalanceTableV1:
    admitted = admit_state(
        FCIS_STATE_SCHEMA_REVISION_V1,
        BALANCE_TABLE_ADMISSION_SCHEMA_ID_V1,
        _limits(),
        _BalanceSourceV1({key: value for key, value in entries}),
    )
    if type(admitted) is not AdmitOk:
        raise AssertionError(f"test balance admission failed: {admitted!r}")
    if type(admitted.value) is not CommittedBalanceTableV1:
        raise AssertionError("test balance admission returned the wrong type")
    return admitted.value


def _lp_balances(
    *entries: tuple[tuple[str, str], int],
) -> CommittedLPTableV1:
    admitted = admit_state(
        FCIS_STATE_SCHEMA_REVISION_V1,
        LP_TABLE_ADMISSION_SCHEMA_ID_V1,
        _limits(),
        _LPSourceV1(
            {key: value for key, value in entries},
            {},
            {},
            {},
            {},
        ),
    )
    if type(admitted) is not AdmitOk:
        raise AssertionError(f"test LP admission failed: {admitted!r}")
    if type(admitted.value) is not CommittedLPTableV1:
        raise AssertionError("test LP admission returned the wrong type")
    return admitted.value


def _pools(
    *pools: CommittedPoolStateV1,
) -> OwnedMapV1[str, CommittedPoolStateV1]:
    admitted = admit_state(
        FCIS_STATE_SCHEMA_REVISION_V1,
        POOL_MAP_ADMISSION_SCHEMA_ID_V1,
        _limits(),
        {pool.pool_id: pool for pool in pools},
    )
    if type(admitted) is not AdmitOk:
        raise AssertionError(f"test pool-map admission failed: {admitted!r}")
    if type(admitted.value) is not OwnedMapV1:
        raise AssertionError("test pool-map admission returned the wrong type")
    return cast(OwnedMapV1[str, CommittedPoolStateV1], admitted.value)


def _context(
    *,
    mode: FCISSettlementModeV1 = FCISSettlementModeV1.STRONG_REPLAY,
    protocol_fee_share_bps: int = 0,
    protocol_fee_recipient_pubkey: str | None = None,
) -> StrongSettlementContextV1:
    admitted = admit_context(
        FCIS_EXECUTION_CONTEXT_SCHEMA_REVISION_V1,
        FCIS_SETTLEMENT_CONTEXT_SCHEMA_ID_V1,
        _limits(),
        FCISSettlementExecutionContextSourceV1(
            now=700,
            min_lp_position_age_seconds=0,
            mode=mode,
            allow_cow_netting=False,
            allow_snapshot_bound_quote_bindings=False,
            protocol_fee_share_bps=protocol_fee_share_bps,
            protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
        ),
    )
    if type(admitted) is not AdmitOk:
        raise AssertionError(f"test context admission failed: {admitted!r}")
    if type(admitted.value) is not FCISSettlementExecutionContextV1:
        raise AssertionError("test context admission returned the wrong type")
    return StrongSettlementContextV1(
        settlement=admitted.value,
        lp_duration_policy=None,
    )


def _empty_pre_state() -> ExactSpotPreStateV1:
    return ExactSpotPreStateV1(
        balances=_balances(),
        pools=_pools(),
        lp_balances=_lp_balances(),
    )


def _funded_pool() -> CommittedPoolStateV1:
    built = build_committed_pool_creation_v1(
        PoolCreationV1(
            pool_id=POOL_ID,
            asset0=ASSET0,
            asset1=ASSET1,
            fee_bps=30,
            created_at=0,
            curve_tag="CPMM",
            curve_params="",
        )
    )
    if type(built) is not PoolCreationBuildOkV1:
        raise AssertionError(f"test pool construction failed: {built!r}")
    return replace(
        built.pool,
        reserve0=INITIAL_RESERVE,
        reserve1=INITIAL_RESERVE,
        lp_supply=INITIAL_LP_SUPPLY,
    )


def _swap_intent() -> OwnedIntentV1:
    return _intent(
        member_ordinal=INTENT_KIND_SWAP_EXACT_IN_ORDINAL,
        kind_name="swap_exact_in",
        intent_id=SWAP_INTENT_ID,
        fields=(
            ("pool_id", POOL_ID),
            ("asset_in", ASSET0),
            ("asset_out", ASSET1),
            ("amount_in", SWAP_AMOUNT_IN),
            ("min_amount_out", 1),
        ),
    )


def _swap_pre_state() -> ExactSpotPreStateV1:
    return ExactSpotPreStateV1(
        balances=_balances(
            ((SENDER, ASSET0), INITIAL_BALANCE),
            ((SENDER, ASSET1), INITIAL_BALANCE),
        ),
        pools=_pools(_funded_pool()),
        lp_balances=_lp_balances(),
    )


def _swap_settlement() -> OwnedSettlementV1:
    action = _fill_action()
    return snapshot_settlement(
        OwnedSettlementV1(
            module="TauSwap",
            version="0.1",
            batch_ref="exact-swap",
            included_intents=((SWAP_INTENT_ID, action),),
            fills=(
                OwnedFillV1(
                    intent_id=SWAP_INTENT_ID,
                    action=action,
                    reason=None,
                    amount_in_filled=SWAP_AMOUNT_IN,
                    amount_out_filled=SWAP_AMOUNT_OUT,
                    fee_paid=SWAP_FEE,
                    protocol_fee_paid=0,
                    amount0_used=None,
                    amount1_used=None,
                    lp_minted=None,
                    amount0_out=None,
                    amount1_out=None,
                    lp_burned=None,
                    reserve_in_before=None,
                    reserve_out_before=None,
                ),
            ),
            balance_deltas=(
                OwnedBalanceDeltaV1(SENDER, ASSET0, 0, SWAP_AMOUNT_IN),
                OwnedBalanceDeltaV1(SENDER, ASSET1, SWAP_AMOUNT_OUT, 0),
            ),
            reserve_deltas=(
                OwnedReserveDeltaV1(POOL_ID, ASSET0, SWAP_AMOUNT_IN, 0),
                OwnedReserveDeltaV1(POOL_ID, ASSET1, 0, SWAP_AMOUNT_OUT),
            ),
            lp_deltas=(),
            events=None,
        )
    )


def _create_pool_intent() -> OwnedIntentV1:
    return _intent(
        member_ordinal=INTENT_KIND_CREATE_POOL_ORDINAL,
        kind_name="create_pool",
        intent_id=CREATE_INTENT_ID,
        fields=(
            ("asset0", ASSET0),
            ("asset1", ASSET1),
            ("fee_bps", 30),
            ("amount0", INITIAL_RESERVE),
            ("amount1", INITIAL_RESERVE),
        ),
    )


def _create_pool_pre_state() -> ExactSpotPreStateV1:
    return ExactSpotPreStateV1(
        balances=_balances(
            ((SENDER, ASSET0), INITIAL_BALANCE),
            ((SENDER, ASSET1), INITIAL_BALANCE),
        ),
        pools=_pools(),
        lp_balances=_lp_balances(),
    )


def _create_pool_event(*, created_at: int = 0):
    return snapshot_owned_json_object(
        {
            "type": "CREATE_POOL",
            "pool_id": POOL_ID,
            "asset0": ASSET0,
            "asset1": ASSET1,
            "fee_bps": 30,
            "curve_tag": "CPMM",
            "curve_params": "",
            "status": "ACTIVE",
            "created_at": created_at,
        }
    )


def _create_pool_settlement() -> OwnedSettlementV1:
    action = _fill_action()
    return snapshot_settlement(
        OwnedSettlementV1(
            module="TauSwap",
            version="0.1",
            batch_ref="exact-create-pool",
            included_intents=((CREATE_INTENT_ID, action),),
            fills=(
                OwnedFillV1(
                    intent_id=CREATE_INTENT_ID,
                    action=action,
                    reason=None,
                    amount_in_filled=None,
                    amount_out_filled=None,
                    fee_paid=None,
                    protocol_fee_paid=None,
                    amount0_used=INITIAL_RESERVE,
                    amount1_used=INITIAL_RESERVE,
                    lp_minted=PROVIDER_LP,
                    amount0_out=None,
                    amount1_out=None,
                    lp_burned=None,
                    reserve_in_before=None,
                    reserve_out_before=None,
                ),
            ),
            balance_deltas=(
                OwnedBalanceDeltaV1(SENDER, ASSET0, 0, INITIAL_RESERVE),
                OwnedBalanceDeltaV1(SENDER, ASSET1, 0, INITIAL_RESERVE),
            ),
            reserve_deltas=(
                OwnedReserveDeltaV1(POOL_ID, ASSET0, INITIAL_RESERVE, 0),
                OwnedReserveDeltaV1(POOL_ID, ASSET1, INITIAL_RESERVE, 0),
            ),
            lp_deltas=(
                OwnedLPDeltaV1(LP_LOCK, POOL_ID, MINIMUM_LP_LOCK, 0),
                OwnedLPDeltaV1(SENDER, POOL_ID, PROVIDER_LP, 0),
            ),
            events=(_create_pool_event(),),
        )
    )


def _exact_out_intent() -> OwnedIntentV1:
    return _intent(
        member_ordinal=INTENT_KIND_SWAP_EXACT_OUT_ORDINAL,
        kind_name="swap_exact_out",
        intent_id=EXACT_OUT_INTENT_ID,
        fields=(
            ("pool_id", POOL_ID),
            ("asset_in", ASSET0),
            ("asset_out", ASSET1),
            ("amount_out", EXACT_OUT_AMOUNT_OUT),
            ("max_amount_in", 10_000),
        ),
    )


def _exact_out_settlement(
    *,
    reserve_witnesses: bool = False,
) -> OwnedSettlementV1:
    action = _fill_action()
    return snapshot_settlement(
        OwnedSettlementV1(
            module="TauSwap",
            version="0.1",
            batch_ref="exact-out",
            included_intents=((EXACT_OUT_INTENT_ID, action),),
            fills=(
                OwnedFillV1(
                    intent_id=EXACT_OUT_INTENT_ID,
                    action=action,
                    reason=None,
                    amount_in_filled=EXACT_OUT_AMOUNT_IN,
                    amount_out_filled=EXACT_OUT_AMOUNT_OUT,
                    fee_paid=EXACT_OUT_FEE,
                    protocol_fee_paid=0,
                    amount0_used=None,
                    amount1_used=None,
                    lp_minted=None,
                    amount0_out=None,
                    amount1_out=None,
                    lp_burned=None,
                    reserve_in_before=INITIAL_RESERVE if reserve_witnesses else None,
                    reserve_out_before=INITIAL_RESERVE if reserve_witnesses else None,
                ),
            ),
            balance_deltas=(
                OwnedBalanceDeltaV1(SENDER, ASSET0, 0, EXACT_OUT_AMOUNT_IN),
                OwnedBalanceDeltaV1(SENDER, ASSET1, EXACT_OUT_AMOUNT_OUT, 0),
            ),
            reserve_deltas=(
                OwnedReserveDeltaV1(POOL_ID, ASSET0, EXACT_OUT_AMOUNT_IN, 0),
                OwnedReserveDeltaV1(POOL_ID, ASSET1, 0, EXACT_OUT_AMOUNT_OUT),
            ),
            lp_deltas=(),
            events=None,
        )
    )


def _liquidity_pre_state() -> ExactSpotPreStateV1:
    return ExactSpotPreStateV1(
        balances=_balances(
            ((SENDER, ASSET0), INITIAL_BALANCE),
            ((SENDER, ASSET1), INITIAL_BALANCE),
        ),
        pools=_pools(_funded_pool()),
        lp_balances=_lp_balances(
            ((LP_LOCK, POOL_ID), MINIMUM_LP_LOCK),
            ((SENDER, POOL_ID), PROVIDER_LP),
        ),
    )


def _add_liquidity_intent() -> OwnedIntentV1:
    return _intent(
        member_ordinal=INTENT_KIND_ADD_LIQUIDITY_ORDINAL,
        kind_name="add_liquidity",
        intent_id=ADD_LIQUIDITY_INTENT_ID,
        fields=(
            ("pool_id", POOL_ID),
            ("amount0_desired", LIQUIDITY_AMOUNT),
            ("amount1_desired", LIQUIDITY_AMOUNT),
            ("amount0_min", 0),
            ("amount1_min", 0),
        ),
    )


def _add_liquidity_settlement() -> OwnedSettlementV1:
    action = _fill_action()
    return snapshot_settlement(
        OwnedSettlementV1(
            module="TauSwap",
            version="0.1",
            batch_ref="add-liquidity",
            included_intents=((ADD_LIQUIDITY_INTENT_ID, action),),
            fills=(
                OwnedFillV1(
                    intent_id=ADD_LIQUIDITY_INTENT_ID,
                    action=action,
                    reason=None,
                    amount_in_filled=None,
                    amount_out_filled=None,
                    fee_paid=None,
                    protocol_fee_paid=None,
                    amount0_used=LIQUIDITY_AMOUNT,
                    amount1_used=LIQUIDITY_AMOUNT,
                    lp_minted=LIQUIDITY_AMOUNT,
                    amount0_out=None,
                    amount1_out=None,
                    lp_burned=None,
                    reserve_in_before=None,
                    reserve_out_before=None,
                ),
            ),
            balance_deltas=(
                OwnedBalanceDeltaV1(SENDER, ASSET0, 0, LIQUIDITY_AMOUNT),
                OwnedBalanceDeltaV1(SENDER, ASSET1, 0, LIQUIDITY_AMOUNT),
            ),
            reserve_deltas=(
                OwnedReserveDeltaV1(POOL_ID, ASSET0, LIQUIDITY_AMOUNT, 0),
                OwnedReserveDeltaV1(POOL_ID, ASSET1, LIQUIDITY_AMOUNT, 0),
            ),
            lp_deltas=(OwnedLPDeltaV1(SENDER, POOL_ID, LIQUIDITY_AMOUNT, 0),),
            events=None,
        )
    )


def _remove_liquidity_intent() -> OwnedIntentV1:
    return _intent(
        member_ordinal=INTENT_KIND_REMOVE_LIQUIDITY_ORDINAL,
        kind_name="remove_liquidity",
        intent_id=REMOVE_LIQUIDITY_INTENT_ID,
        fields=(
            ("pool_id", POOL_ID),
            ("lp_amount", REMOVE_LP_AMOUNT),
            ("amount0_min", 0),
            ("amount1_min", 0),
        ),
    )


def _remove_liquidity_settlement() -> OwnedSettlementV1:
    action = _fill_action()
    return snapshot_settlement(
        OwnedSettlementV1(
            module="TauSwap",
            version="0.1",
            batch_ref="remove-liquidity",
            included_intents=((REMOVE_LIQUIDITY_INTENT_ID, action),),
            fills=(
                OwnedFillV1(
                    intent_id=REMOVE_LIQUIDITY_INTENT_ID,
                    action=action,
                    reason=None,
                    amount_in_filled=None,
                    amount_out_filled=None,
                    fee_paid=None,
                    protocol_fee_paid=None,
                    amount0_used=None,
                    amount1_used=None,
                    lp_minted=None,
                    amount0_out=REMOVE_LP_AMOUNT,
                    amount1_out=REMOVE_LP_AMOUNT,
                    lp_burned=REMOVE_LP_AMOUNT,
                    reserve_in_before=None,
                    reserve_out_before=None,
                ),
            ),
            balance_deltas=(
                OwnedBalanceDeltaV1(SENDER, ASSET0, REMOVE_LP_AMOUNT, 0),
                OwnedBalanceDeltaV1(SENDER, ASSET1, REMOVE_LP_AMOUNT, 0),
            ),
            reserve_deltas=(
                OwnedReserveDeltaV1(POOL_ID, ASSET0, 0, REMOVE_LP_AMOUNT),
                OwnedReserveDeltaV1(POOL_ID, ASSET1, 0, REMOVE_LP_AMOUNT),
            ),
            lp_deltas=(OwnedLPDeltaV1(SENDER, POOL_ID, 0, REMOVE_LP_AMOUNT),),
            events=None,
        )
    )


def _ordinary_reject_settlement() -> OwnedSettlementV1:
    return snapshot_settlement(
        OwnedSettlementV1(
            module="TauSwap",
            version="0.1",
            batch_ref="ordinary-reject",
            included_intents=((SWAP_INTENT_ID, _reject_action()),),
            fills=(),
            balance_deltas=(),
            reserve_deltas=(),
            lp_deltas=(),
            events=None,
        )
    )


def _proof_carrying_context() -> StrongSettlementContextV1:
    return _context(mode=FCISSettlementModeV1.STRONG_PROOF_CARRYING)


def _protocol_fee_context(
    recipient: str = FEE_RECIPIENT,
) -> StrongSettlementContextV1:
    return _context(
        protocol_fee_share_bps=5_000,
        protocol_fee_recipient_pubkey=recipient,
    )


def _protocol_fee_settlement() -> OwnedSettlementV1:
    action = _fill_action()
    return snapshot_settlement(
        OwnedSettlementV1(
            module="TauSwap",
            version="0.1",
            batch_ref="protocol-fee",
            included_intents=((SWAP_INTENT_ID, action),),
            fills=(
                OwnedFillV1(
                    intent_id=SWAP_INTENT_ID,
                    action=action,
                    reason=None,
                    amount_in_filled=SWAP_AMOUNT_IN,
                    amount_out_filled=SWAP_AMOUNT_OUT,
                    fee_paid=SWAP_FEE,
                    protocol_fee_paid=1,
                    amount0_used=None,
                    amount1_used=None,
                    lp_minted=None,
                    amount0_out=None,
                    amount1_out=None,
                    lp_burned=None,
                    reserve_in_before=None,
                    reserve_out_before=None,
                ),
            ),
            balance_deltas=(
                OwnedBalanceDeltaV1(SENDER, ASSET0, 0, SWAP_AMOUNT_IN),
                OwnedBalanceDeltaV1(SENDER, ASSET1, SWAP_AMOUNT_OUT, 0),
                OwnedBalanceDeltaV1(FEE_RECIPIENT, ASSET0, 1, 0),
            ),
            reserve_deltas=(
                OwnedReserveDeltaV1(POOL_ID, ASSET0, SWAP_AMOUNT_IN - 1, 0),
                OwnedReserveDeltaV1(POOL_ID, ASSET1, 0, SWAP_AMOUNT_OUT),
            ),
            lp_deltas=(),
            events=None,
        )
    )


def _protocol_fee_exact_out_settlement() -> OwnedSettlementV1:
    action = _fill_action()
    protocol_fee_paid = 2
    return snapshot_settlement(
        OwnedSettlementV1(
            module="TauSwap",
            version="0.1",
            batch_ref="protocol-fee-exact-out",
            included_intents=((EXACT_OUT_INTENT_ID, action),),
            fills=(
                OwnedFillV1(
                    intent_id=EXACT_OUT_INTENT_ID,
                    action=action,
                    reason=None,
                    amount_in_filled=EXACT_OUT_AMOUNT_IN,
                    amount_out_filled=EXACT_OUT_AMOUNT_OUT,
                    fee_paid=EXACT_OUT_FEE,
                    protocol_fee_paid=protocol_fee_paid,
                    amount0_used=None,
                    amount1_used=None,
                    lp_minted=None,
                    amount0_out=None,
                    amount1_out=None,
                    lp_burned=None,
                    reserve_in_before=None,
                    reserve_out_before=None,
                ),
            ),
            balance_deltas=(
                OwnedBalanceDeltaV1(SENDER, ASSET0, 0, EXACT_OUT_AMOUNT_IN),
                OwnedBalanceDeltaV1(SENDER, ASSET1, EXACT_OUT_AMOUNT_OUT, 0),
                OwnedBalanceDeltaV1(
                    FEE_RECIPIENT,
                    ASSET0,
                    protocol_fee_paid,
                    0,
                ),
            ),
            reserve_deltas=(
                OwnedReserveDeltaV1(
                    POOL_ID,
                    ASSET0,
                    EXACT_OUT_AMOUNT_IN - protocol_fee_paid,
                    0,
                ),
                OwnedReserveDeltaV1(POOL_ID, ASSET1, 0, EXACT_OUT_AMOUNT_OUT),
            ),
            lp_deltas=(),
            events=None,
        )
    )


def _recipient_swap_intent() -> OwnedIntentV1:
    return _intent(
        member_ordinal=INTENT_KIND_SWAP_EXACT_IN_ORDINAL,
        kind_name="swap_exact_in",
        intent_id=SWAP_INTENT_ID,
        fields=(
            ("recipient", RECIPIENT),
            ("pool_id", POOL_ID),
            ("asset_in", ASSET0),
            ("asset_out", ASSET1),
            ("amount_in", SWAP_AMOUNT_IN),
            ("min_amount_out", 1),
        ),
    )


def _recipient_swap_settlement() -> OwnedSettlementV1:
    action = _fill_action()
    return snapshot_settlement(
        OwnedSettlementV1(
            module="TauSwap",
            version="0.1",
            batch_ref="recipient-swap",
            included_intents=((SWAP_INTENT_ID, action),),
            fills=(
                OwnedFillV1(
                    intent_id=SWAP_INTENT_ID,
                    action=action,
                    reason=None,
                    amount_in_filled=SWAP_AMOUNT_IN,
                    amount_out_filled=SWAP_AMOUNT_OUT,
                    fee_paid=SWAP_FEE,
                    protocol_fee_paid=0,
                    amount0_used=None,
                    amount1_used=None,
                    lp_minted=None,
                    amount0_out=None,
                    amount1_out=None,
                    lp_burned=None,
                    reserve_in_before=None,
                    reserve_out_before=None,
                ),
            ),
            balance_deltas=(
                OwnedBalanceDeltaV1(SENDER, ASSET0, 0, SWAP_AMOUNT_IN),
                OwnedBalanceDeltaV1(RECIPIENT, ASSET1, SWAP_AMOUNT_OUT, 0),
            ),
            reserve_deltas=(
                OwnedReserveDeltaV1(POOL_ID, ASSET0, SWAP_AMOUNT_IN, 0),
                OwnedReserveDeltaV1(POOL_ID, ASSET1, 0, SWAP_AMOUNT_OUT),
            ),
            lp_deltas=(),
            events=None,
        )
    )


def _evaluate(
    settlement: OwnedSettlementV1,
    intents: tuple[OwnedIntentV1, ...],
    pre_state: ExactSpotPreStateV1,
    *,
    context: StrongSettlementContextV1 | None = None,
):
    exact_context = _context() if context is None else context
    return evaluate_settlement_strong_exact_v1(
        settlement=settlement,
        intents=intents,
        pre_state=pre_state,
        context=exact_context,
    )


def _assert_reject(result, expected_text: str) -> None:
    assert type(result.result) is ExactStrongSettlementRejectV1
    assert expected_text in result.result.reason
    assert not hasattr(result.result, "balances")
    assert not hasattr(result.result, "balance_patch")


def test_empty_settlement_returns_unchanged_candidate_without_patches() -> None:
    pre_state = _empty_pre_state()
    settlement = snapshot_settlement(
        OwnedSettlementV1(
            module="TauSwap",
            version="0.1",
            batch_ref="empty",
            included_intents=(),
            fills=(),
            balance_deltas=(),
            reserve_deltas=(),
            lp_deltas=(),
            events=None,
        )
    )

    observed = _evaluate(settlement, (), pre_state)

    assert type(observed.result) is ExactStrongSettlementCandidateV1
    assert observed.result.balances == pre_state.balances
    assert observed.result.pools == pre_state.pools
    assert observed.result.lp_balances == pre_state.lp_balances
    assert observed.result.balance_patch is None
    assert observed.result.pool_patch is None
    assert observed.result.lp_patch is None
    assert observed.state_read_trace.balance_keys == ()
    assert observed.state_read_trace.pool_ids == ()
    assert observed.state_read_trace.lp_keys == ()


def test_exact_in_swap_returns_the_exact_successor_and_patches() -> None:
    observed = _evaluate(
        _swap_settlement(),
        (_swap_intent(),),
        _swap_pre_state(),
    )

    assert type(observed.result) is ExactStrongSettlementCandidateV1
    candidate = observed.result
    assert candidate.balances.get(SENDER, ASSET0) == INITIAL_BALANCE - SWAP_AMOUNT_IN
    assert candidate.balances.get(SENDER, ASSET1) == INITIAL_BALANCE + SWAP_AMOUNT_OUT
    assert candidate.pools[POOL_ID].reserve0 == INITIAL_RESERVE + SWAP_AMOUNT_IN
    assert candidate.pools[POOL_ID].reserve1 == INITIAL_RESERVE - SWAP_AMOUNT_OUT
    assert candidate.balance_patch is not None
    assert candidate.pool_patch is not None
    assert candidate.lp_patch is None
    assert observed.state_read_trace.pool_ids == (POOL_ID,)


def test_create_pool_accepts_only_the_exact_event_projection() -> None:
    observed = _evaluate(
        _create_pool_settlement(),
        (_create_pool_intent(),),
        _create_pool_pre_state(),
    )

    assert type(observed.result) is ExactStrongSettlementCandidateV1
    candidate = observed.result
    assert candidate.balances.get(SENDER, ASSET0) == INITIAL_BALANCE - INITIAL_RESERVE
    assert candidate.balances.get(SENDER, ASSET1) == INITIAL_BALANCE - INITIAL_RESERVE
    assert candidate.pools[POOL_ID].reserve0 == INITIAL_RESERVE
    assert candidate.pools[POOL_ID].reserve1 == INITIAL_RESERVE
    assert candidate.pools[POOL_ID].lp_supply == INITIAL_LP_SUPPLY
    assert candidate.lp_balances.get(LP_LOCK, POOL_ID) == MINIMUM_LP_LOCK
    assert candidate.lp_balances.get(SENDER, POOL_ID) == PROVIDER_LP
    assert candidate.balance_patch is not None
    assert candidate.pool_patch is not None
    assert candidate.lp_patch is not None

    wrong_event = replace(
        _create_pool_settlement(),
        events=(_create_pool_event(created_at=1),),
    )
    rejected = _evaluate(
        wrong_event,
        (_create_pool_intent(),),
        _create_pool_pre_state(),
    )
    _assert_reject(rejected, "events mismatch")


def test_malformed_fill_rejects_without_candidate_authority() -> None:
    settlement = _swap_settlement()
    malformed_fill = replace(
        settlement.fills[0],
        amount_out_filled=SWAP_AMOUNT_OUT + 1,
    )
    malformed = replace(settlement, fills=(malformed_fill,))

    observed = _evaluate(
        malformed,
        (_swap_intent(),),
        _swap_pre_state(),
    )

    _assert_reject(observed, "swap amount_out_filled mismatch")


def test_malformed_delta_rejects_without_candidate_authority() -> None:
    settlement = _swap_settlement()
    malformed_output = replace(
        settlement.balance_deltas[1],
        delta_add=SWAP_AMOUNT_OUT - 1,
    )
    malformed = replace(
        settlement,
        balance_deltas=(settlement.balance_deltas[0], malformed_output),
    )

    observed = _evaluate(
        malformed,
        (_swap_intent(),),
        _swap_pre_state(),
    )

    _assert_reject(observed, "balance_deltas")


def test_unexpected_event_rejects_without_candidate_authority() -> None:
    malformed = replace(
        _swap_settlement(),
        events=(snapshot_owned_json_object({"type": "UNEXPECTED"}),),
    )

    observed = _evaluate(
        malformed,
        (_swap_intent(),),
        _swap_pre_state(),
    )

    _assert_reject(observed, "events mismatch")


def test_hostile_nested_prestate_mutation_rejects_before_candidate_creation() -> None:
    pre_state = _swap_pre_state()
    pool = pre_state.pools[POOL_ID]
    object.__setattr__(pool, "reserve0", -1)

    observed = _evaluate(
        _swap_settlement(),
        (_swap_intent(),),
        pre_state,
    )

    _assert_reject(observed, "pre-state")
    assert observed.state_read_trace.balance_keys == ()
    assert observed.state_read_trace.pool_ids == ()
    assert observed.state_read_trace.lp_keys == ()


def test_equal_exact_inputs_produce_equal_result_and_trace() -> None:
    settlement = _swap_settlement()
    intents = (_swap_intent(),)
    pre_state = _swap_pre_state()

    first = _evaluate(settlement, intents, pre_state)
    second = _evaluate(settlement, intents, pre_state)

    assert first == second
    assert first.result == second.result
    assert first.state_read_trace == second.state_read_trace


def test_wrong_variant_swap_fill_field_rejects_exactly() -> None:
    settlement = _swap_settlement()
    wrong_fill = replace(
        settlement.fills[0],
        lp_minted=1,
    )
    observed = _evaluate(
        replace(settlement, fills=(wrong_fill,)),
        (_swap_intent(),),
        _swap_pre_state(),
    )

    _assert_reject(observed, "swap fill contains wrong-variant fields")
    assert observed.result.reason == (
        f"swap fill contains wrong-variant fields for intent_id={SWAP_INTENT_ID}"
    )


def test_protocol_fee_recipient_substitution_rejects_exactly() -> None:
    observed = _evaluate(
        _protocol_fee_settlement(),
        (_swap_intent(),),
        _swap_pre_state(),
        context=_protocol_fee_context(OTHER_FEE_RECIPIENT),
    )

    _assert_reject(observed, "balance_deltas mismatch vs replay")
    assert observed.result.reason == "balance_deltas mismatch vs replay"
