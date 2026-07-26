"""Complete command/context-bound pre-state support commitment for FCIS v5."""

from __future__ import annotations

from dataclasses import dataclass
from typing import final

from ..state.canonical import (
    domain_sep_bytes,
    encode_bytes,
    encode_uvarint,
    hex_to_bytes_fixed,
    sha256_hex,
)
from ..state.committed_spot_roots import _encode_pool_body_v1
from ..state.fcis_execution_context import admit_fcis_step_execution_context_v1
from ..state.fcis_execution_context_codec import encode_fcis_execution_context_v1
from ..state.fcis_execution_context_schema import (
    FCIS_FEE_SPLIT_POLICY_FIELD_NAMES_V1,
    FCIS_LP_DURATION_POLICY_FIELD_NAMES_V1,
    FCIS_SETTLEMENT_CONTEXT_FIELD_NAMES_V1,
)
from ..state.fcis_execution_context_values import (
    FCIS_STEP_CONTEXT_SCHEMA_ID_V1,
    FCISStepExecutionContextV1,
)
from ..state.intent_field_registry import intent_allowed_field_names_v1
from ..state.intent_snapshots import (
    OwnedIntentV1,
    _canonical_owned_intent_bytes_admitted_v1,
    admit_intent_batch,
    owned_intent_field_v1,
    owned_intent_kind_text_v1,
)
from ..state.intents import IntentKind
from ..state.owned_collections import OwnedMapV1
from ..state.pools import compute_pool_id, normalize_curve_config
from ..state.snapshot_combinators import AdmitOk
from ..state.state_snapshot_values import (
    CommittedBalanceTableV1,
    CommittedFeeAccumulatorStateV1,
    CommittedLPTableV1,
    CommittedNonceTableV1,
    CommittedPoolStateV1,
)
from ..state.state_snapshots import (
    snapshot_balance_table,
    snapshot_fee_accumulator,
    snapshot_lp_table,
    snapshot_nonce_table,
    snapshot_pool_map,
)
from ..state.support_root import LP_LOCK_PUBKEY, _route_support_pool_ids_owned_v1
from .fcis_state_read_trace_v5 import FCISContextReadTraceV5, FCISStateReadTraceV5
from .fcis_support_profile_constants_v5 import (
    FCIS_SUPPORT_PROFILE_COMPLETE_V5,
    FCIS_SUPPORT_PROFILE_ID_V5,
    FCIS_SUPPORT_PROFILE_VERSION_V5,
)
from .settlement_snapshots import (
    OwnedSettlementV1,
    _canonical_owned_settlement_bytes_admitted_v1,
    snapshot_settlement,
)

FCIS_SUPPORT_SET_DOMAIN_V5 = "fcis_support_set"
FCIS_SUPPORT_COMMAND_DOMAIN_V5 = "fcis_support_command"
FCIS_SUPPORT_CONTEXT_HASH_DOMAIN_V1 = "fcis_step_execution_context"
FCIS_SUPPORT_ROOT_DOMAIN_V5 = "state_support_root"

_FCIS_TOP_LEVEL_CONTEXT_PATHS_V5 = (
    "require_all_nonces",
    "reject_settlements_with_rejected_intents",
    "snapshot_version",
)
FCIS_SUPPORT_CONTEXT_PATHS_V5 = tuple(
    sorted(
        tuple(f"settlement.{name}" for name in FCIS_SETTLEMENT_CONTEXT_FIELD_NAMES_V1)
        + _FCIS_TOP_LEVEL_CONTEXT_PATHS_V5
        + ("fee_split_policy",)
        + tuple(f"fee_split_policy.{name}" for name in FCIS_FEE_SPLIT_POLICY_FIELD_NAMES_V1)
        + ("lp_duration_policy",)
        + tuple(f"lp_duration_policy.{name}" for name in FCIS_LP_DURATION_POLICY_FIELD_NAMES_V1)
    )
)

# The declared context support is the complete closed schema. Evaluation emits
# a separate FCISContextReadTraceV5 by explicitly projecting those fields.
FCIS_CONTEXT_SCHEMA_PATHS_V5 = FCIS_SUPPORT_CONTEXT_PATHS_V5


FCIS_SUPPORT_INTENT_FIELD_INVENTORY_V5 = tuple(
    (kind.value, intent_allowed_field_names_v1(kind)) for kind in IntentKind
)
FCIS_SUPPORT_FIELD_DEPENDENCIES_V5 = (
    (
        IntentKind.CREATE_POOL.value,
        ("nonce", "asset0", "asset1", "fee_bps", "curve_tag", "curve_params"),
    ),
    (IntentKind.ADD_LIQUIDITY.value, ("nonce", "recipient", "pool_id")),
    (IntentKind.REMOVE_LIQUIDITY.value, ("nonce", "recipient", "pool_id")),
    (
        IntentKind.SWAP_EXACT_IN.value,
        ("nonce", "recipient", "pool_id", "asset_in", "asset_out"),
    ),
    (
        IntentKind.SWAP_EXACT_OUT.value,
        ("nonce", "recipient", "pool_id", "asset_in", "asset_out"),
    ),
    (
        IntentKind.ROUTE_EXACT_IN.value,
        (
            "nonce",
            "recipient",
            "asset_in",
            "asset_out",
            "route_legs",
            "route_pool_fingerprints",
        ),
    ),
    (
        IntentKind.ROUTE_EXACT_OUT.value,
        (
            "nonce",
            "recipient",
            "asset_in",
            "asset_out",
            "route_legs",
            "route_pool_fingerprints",
        ),
    ),
)

FCIS_SUPPORT_COMMAND_ONLY_FIELDS_V5 = (
    (
        IntentKind.CREATE_POOL.value,
        (
            "recipient",
            "submission_order",
            "quote_receipt_hash",
            "quote_pool_fingerprint",
            "quote_receipt_leg_index",
            "oracle_authorization",
            "amount0",
            "amount1",
            "created_at",
        ),
    ),
    (
        IntentKind.ADD_LIQUIDITY.value,
        (
            "submission_order",
            "quote_receipt_hash",
            "quote_pool_fingerprint",
            "quote_receipt_leg_index",
            "oracle_authorization",
            "amount0_desired",
            "amount1_desired",
            "amount0_min",
            "amount1_min",
        ),
    ),
    (
        IntentKind.REMOVE_LIQUIDITY.value,
        (
            "submission_order",
            "quote_receipt_hash",
            "quote_pool_fingerprint",
            "quote_receipt_leg_index",
            "oracle_authorization",
            "lp_amount",
            "amount0_min",
            "amount1_min",
        ),
    ),
    (
        IntentKind.SWAP_EXACT_IN.value,
        (
            "submission_order",
            "quote_receipt_hash",
            "quote_pool_fingerprint",
            "quote_receipt_leg_index",
            "oracle_authorization",
            "amount_in",
            "min_amount_out",
        ),
    ),
    (
        IntentKind.SWAP_EXACT_OUT.value,
        (
            "submission_order",
            "quote_receipt_hash",
            "quote_pool_fingerprint",
            "quote_receipt_leg_index",
            "oracle_authorization",
            "amount_out",
            "max_amount_in",
        ),
    ),
    (
        IntentKind.ROUTE_EXACT_IN.value,
        (
            "submission_order",
            "quote_receipt_hash",
            "quote_pool_fingerprint",
            "quote_receipt_leg_index",
            "oracle_authorization",
            "leg_indices",
            "total_amount_in",
            "total_min_amount_out",
        ),
    ),
    (
        IntentKind.ROUTE_EXACT_OUT.value,
        (
            "submission_order",
            "quote_receipt_hash",
            "quote_pool_fingerprint",
            "quote_receipt_leg_index",
            "oracle_authorization",
            "leg_indices",
            "total_amount_out",
            "total_max_amount_in",
        ),
    ),
)


def _validate_support_field_inventory_v5() -> None:
    allowed_by_kind = dict(FCIS_SUPPORT_INTENT_FIELD_INVENTORY_V5)
    dependency_by_kind = dict(FCIS_SUPPORT_FIELD_DEPENDENCIES_V5)
    command_only_by_kind = dict(FCIS_SUPPORT_COMMAND_ONLY_FIELDS_V5)
    expected_kinds = tuple(kind.value for kind in IntentKind)
    if expected_kinds != tuple(allowed_by_kind):
        raise RuntimeError("FCIS v5 intent inventory drift")
    if expected_kinds != tuple(dependency_by_kind):
        raise RuntimeError("FCIS v5 support dependency inventory drift")
    if expected_kinds != tuple(command_only_by_kind):
        raise RuntimeError("FCIS v5 command-only inventory drift")
    for kind in expected_kinds:
        allowed = tuple(allowed_by_kind[kind])
        dependencies = tuple(dependency_by_kind[kind])
        command_only = tuple(command_only_by_kind[kind])
        if len(dependencies) != len(set(dependencies)):
            raise RuntimeError(f"FCIS v5 duplicate support dependency for {kind}")
        if len(command_only) != len(set(command_only)):
            raise RuntimeError(f"FCIS v5 duplicate command-only field for {kind}")
        if set(dependencies) & set(command_only):
            raise RuntimeError(f"FCIS v5 field has two classifications for {kind}")
        if set(dependencies) | set(command_only) != set(allowed):
            raise RuntimeError(f"FCIS v5 field classification is incomplete for {kind}")


_validate_support_field_inventory_v5()


def _validate_pair_tuple_v5(name: str, values: tuple[tuple[str, str], ...]) -> None:
    if type(values) is not tuple:
        raise TypeError(f"{name} must be an exact tuple")
    for value in values:
        if (
            type(value) is not tuple
            or len(value) != 2
            or type(value[0]) is not str
            or not value[0]
            or type(value[1]) is not str
            or not value[1]
        ):
            raise TypeError(f"{name} must contain exact nonempty string pairs")
    if values != tuple(sorted(values)) or len(values) != len(set(values)):
        raise ValueError(f"{name} must be canonical and duplicate-free")


def _validate_string_tuple_v5(name: str, values: tuple[str, ...]) -> None:
    if type(values) is not tuple or any(type(value) is not str or not value for value in values):
        raise TypeError(f"{name} must be an exact tuple of nonempty strings")
    if values != tuple(sorted(values)) or len(values) != len(set(values)):
        raise ValueError(f"{name} must be canonical and duplicate-free")


@final
@dataclass(frozen=True, slots=True)
class FCISSupportSetV5:
    balance_keys: tuple[tuple[str, str], ...]
    pool_ids: tuple[str, ...]
    lp_keys: tuple[tuple[str, str], ...]
    nonce_keys: tuple[str, ...]
    include_fee_accumulator: bool
    context_paths: tuple[str, ...]

    def __post_init__(self) -> None:
        _validate_pair_tuple_v5("support balance keys", self.balance_keys)
        _validate_string_tuple_v5("support pool ids", self.pool_ids)
        _validate_pair_tuple_v5("support LP keys", self.lp_keys)
        _validate_string_tuple_v5("support nonce keys", self.nonce_keys)
        if type(self.include_fee_accumulator) is not bool:
            raise TypeError("support fee flag must be an exact bool")
        _validate_string_tuple_v5("support context paths", self.context_paths)


@final
@dataclass(frozen=True, slots=True)
class FCISSequentialReadTraceV5:
    balance_keys: tuple[tuple[str, str], ...]
    pool_ids: tuple[str, ...]
    lp_keys: tuple[tuple[str, str], ...]
    nonce_keys: tuple[str, ...]
    reads_fee_accumulator: bool
    context_paths: tuple[str, ...]

    def __post_init__(self) -> None:
        _validate_pair_tuple_v5("trace balance keys", self.balance_keys)
        _validate_string_tuple_v5("trace pool ids", self.pool_ids)
        _validate_pair_tuple_v5("trace LP keys", self.lp_keys)
        _validate_string_tuple_v5("trace nonce keys", self.nonce_keys)
        if type(self.reads_fee_accumulator) is not bool:
            raise TypeError("trace fee flag must be an exact bool")
        _validate_string_tuple_v5("trace context paths", self.context_paths)


@final
@dataclass(frozen=True, slots=True)
class FCISSupportRootEvidenceV5:
    support: FCISSupportSetV5
    trace: FCISSequentialReadTraceV5
    support_set_preimage: bytes
    support_set_commitment: str
    command_root: str
    execution_context_hash: str
    root_preimage: bytes
    root: str

    def __post_init__(self) -> None:
        if type(self.support) is not FCISSupportSetV5:
            raise TypeError("support-root evidence requires an exact support set")
        if type(self.trace) is not FCISSequentialReadTraceV5:
            raise TypeError("support-root evidence requires an exact read trace")
        if not support_contains_trace_v5(self.support, self.trace):
            raise ValueError("support-root read trace escapes declared support")
        if type(self.support_set_preimage) is not bytes or type(self.root_preimage) is not bytes:
            raise TypeError("support-root preimages must be exact bytes")
        for digest in (
            self.support_set_commitment,
            self.command_root,
            self.execution_context_hash,
            self.root,
        ):
            hex_to_bytes_fixed(digest, nbytes=32, name="support digest")
        if sha256_hex(self.support_set_preimage) != self.support_set_commitment:
            raise ValueError("support-set commitment does not match its preimage")
        if sha256_hex(self.root_preimage) != self.root:
            raise ValueError("support root does not match its preimage")


@final
@dataclass(frozen=True, slots=True)
class _SupportFragmentV5:
    balance_keys: tuple[tuple[str, str], ...] = ()
    pool_ids: tuple[str, ...] = ()
    lp_keys: tuple[tuple[str, str], ...] = ()
    nonce_keys: tuple[str, ...] = ()


def _required_text_field_v5(intent: OwnedIntentV1, name: str) -> str:
    value = owned_intent_field_v1(intent, name, None)
    if type(value) is not str or not value:
        raise ValueError(f"support requires nonempty {name}")
    return value


def _recipient_v5(intent: OwnedIntentV1) -> str:
    recipient = owned_intent_field_v1(intent, "recipient", intent.sender_pubkey)
    if type(recipient) is not str or not recipient:
        raise ValueError("support requires a nonempty recipient")
    return recipient


def _created_pool_id_v5(intent: OwnedIntentV1) -> str:
    asset0 = _required_text_field_v5(intent, "asset0")
    asset1 = _required_text_field_v5(intent, "asset1")
    fee_bps = owned_intent_field_v1(intent, "fee_bps", None)
    if type(fee_bps) is not int:
        raise TypeError("support requires an exact create-pool fee")
    normalized_tag, normalized_params = normalize_curve_config(
        curve_tag=owned_intent_field_v1(intent, "curve_tag", None),
        curve_params=owned_intent_field_v1(intent, "curve_params", None),
    )
    return compute_pool_id(
        asset0,
        asset1,
        fee_bps,
        curve_tag=normalized_tag,
        curve_params=normalized_params,
    )


def _created_pool_assets_v5(
    intents: tuple[OwnedIntentV1, ...],
) -> dict[str, tuple[str, str]]:
    created: dict[str, tuple[str, str]] = {}
    for intent in intents:
        if owned_intent_kind_text_v1(intent) != IntentKind.CREATE_POOL.value:
            continue
        pool_id = _created_pool_id_v5(intent)
        assets = (
            _required_text_field_v5(intent, "asset0"),
            _required_text_field_v5(intent, "asset1"),
        )
        prior = created.get(pool_id)
        if prior is not None and prior != assets:
            raise ValueError("created-pool identifier collision in support derivation")
        created[pool_id] = assets
    return created


def _protocol_fee_balance_key_v5(
    context: FCISStepExecutionContextV1,
    asset_in: str,
) -> tuple[tuple[str, str], ...]:
    settlement_context = context.settlement
    if settlement_context.protocol_fee_share_bps == 0:
        return ()
    recipient = settlement_context.protocol_fee_recipient_pubkey
    if type(recipient) is not str or not recipient:
        raise ValueError("protocol fee support requires its recipient")
    return ((recipient, asset_in),)


def _create_pool_fragment_v5(intent: OwnedIntentV1) -> _SupportFragmentV5:
    asset0 = _required_text_field_v5(intent, "asset0")
    asset1 = _required_text_field_v5(intent, "asset1")
    pool_id = _created_pool_id_v5(intent)
    return _SupportFragmentV5(
        balance_keys=((intent.sender_pubkey, asset0), (intent.sender_pubkey, asset1)),
        pool_ids=(pool_id,),
        lp_keys=((LP_LOCK_PUBKEY, pool_id), (intent.sender_pubkey, pool_id)),
        nonce_keys=(intent.sender_pubkey,),
    )


def _pool_assets_v5(
    pool_id: str,
    pools: OwnedMapV1[str, CommittedPoolStateV1],
    created_pool_assets: dict[str, tuple[str, str]],
) -> tuple[str, str] | None:
    pool = pools.get(pool_id)
    if pool is not None:
        return pool.asset0, pool.asset1
    return created_pool_assets.get(pool_id)


def _liquidity_fragment_v5(
    intent: OwnedIntentV1,
    pools: OwnedMapV1[str, CommittedPoolStateV1],
    created_pool_assets: dict[str, tuple[str, str]],
) -> _SupportFragmentV5:
    pool_id = _required_text_field_v5(intent, "pool_id")
    kind = owned_intent_kind_text_v1(intent)
    recipient = _recipient_v5(intent)
    assets = _pool_assets_v5(pool_id, pools, created_pool_assets)
    if kind == IntentKind.ADD_LIQUIDITY.value:
        balances = (
            ()
            if assets is None
            else (
                (intent.sender_pubkey, assets[0]),
                (intent.sender_pubkey, assets[1]),
            )
        )
        return _SupportFragmentV5(
            balance_keys=balances,
            pool_ids=(pool_id,),
            lp_keys=((recipient, pool_id),),
            nonce_keys=(intent.sender_pubkey,),
        )
    if kind == IntentKind.REMOVE_LIQUIDITY.value:
        balances = () if assets is None else ((recipient, assets[0]), (recipient, assets[1]))
        return _SupportFragmentV5(
            balance_keys=balances,
            pool_ids=(pool_id,),
            lp_keys=((intent.sender_pubkey, pool_id),),
            nonce_keys=(intent.sender_pubkey,),
        )
    raise ValueError("liquidity fragment received an unsupported intent kind")


def _swap_fragment_v5(
    intent: OwnedIntentV1,
    context: FCISStepExecutionContextV1,
) -> _SupportFragmentV5:
    sender = intent.sender_pubkey
    recipient = _recipient_v5(intent)
    asset_in = _required_text_field_v5(intent, "asset_in")
    asset_out = _required_text_field_v5(intent, "asset_out")
    balances = {
        (sender, asset_in),
        (recipient, asset_out),
        *_protocol_fee_balance_key_v5(context, asset_in),
    }
    return _SupportFragmentV5(
        balance_keys=tuple(sorted(balances)),
        pool_ids=(_required_text_field_v5(intent, "pool_id"),),
        nonce_keys=(sender,),
    )


def _route_fragment_v5(
    intent: OwnedIntentV1,
    context: FCISStepExecutionContextV1,
) -> _SupportFragmentV5:
    sender = intent.sender_pubkey
    recipient = _recipient_v5(intent)
    asset_in = _required_text_field_v5(intent, "asset_in")
    asset_out = _required_text_field_v5(intent, "asset_out")
    balances = {
        (sender, asset_in),
        (recipient, asset_out),
        *_protocol_fee_balance_key_v5(context, asset_in),
    }
    return _SupportFragmentV5(
        balance_keys=tuple(sorted(balances)),
        pool_ids=_route_support_pool_ids_owned_v1(intent),
        nonce_keys=(sender,),
    )


def _intent_fragment_v5(
    intent: OwnedIntentV1,
    pools: OwnedMapV1[str, CommittedPoolStateV1],
    created_pool_assets: dict[str, tuple[str, str]],
    context: FCISStepExecutionContextV1,
) -> _SupportFragmentV5:
    kind = owned_intent_kind_text_v1(intent)
    if kind == IntentKind.CREATE_POOL.value:
        return _create_pool_fragment_v5(intent)
    if kind in (IntentKind.ADD_LIQUIDITY.value, IntentKind.REMOVE_LIQUIDITY.value):
        return _liquidity_fragment_v5(intent, pools, created_pool_assets)
    if kind in (IntentKind.SWAP_EXACT_IN.value, IntentKind.SWAP_EXACT_OUT.value):
        return _swap_fragment_v5(intent, context)
    if kind in (IntentKind.ROUTE_EXACT_IN.value, IntentKind.ROUTE_EXACT_OUT.value):
        return _route_fragment_v5(intent, context)
    raise ValueError("unsupported intent kind in support profile v5")


def _validate_support_derivation_inputs_v5(
    intents: tuple[OwnedIntentV1, ...],
    pools: OwnedMapV1[str, CommittedPoolStateV1],
    context: FCISStepExecutionContextV1,
) -> None:
    if type(intents) is not tuple or any(type(item) is not OwnedIntentV1 for item in intents):
        raise TypeError("support derivation requires an exact owned intent tuple")
    if type(pools) is not OwnedMapV1:
        raise TypeError("support derivation requires an exact owned pool map")
    if type(context) is not FCISStepExecutionContextV1:
        raise TypeError("support derivation requires an exact execution context")


def _support_set_from_fragments_v5(
    fragments: tuple[_SupportFragmentV5, ...],
    context: FCISStepExecutionContextV1,
) -> FCISSupportSetV5:
    return FCISSupportSetV5(
        balance_keys=tuple(sorted({key for item in fragments for key in item.balance_keys})),
        pool_ids=tuple(sorted({key for item in fragments for key in item.pool_ids})),
        lp_keys=tuple(sorted({key for item in fragments for key in item.lp_keys})),
        nonce_keys=tuple(sorted({key for item in fragments for key in item.nonce_keys})),
        include_fee_accumulator=context.fee_split_policy is not None,
        context_paths=FCIS_SUPPORT_CONTEXT_PATHS_V5,
    )


def _derive_fcis_support_set_v5_admitted(
    *,
    intents: tuple[OwnedIntentV1, ...],
    pools: OwnedMapV1[str, CommittedPoolStateV1],
    context: FCISStepExecutionContextV1,
) -> FCISSupportSetV5:
    _validate_support_derivation_inputs_v5(intents, pools, context)
    created_pool_assets = _created_pool_assets_v5(intents)
    fragments = tuple(
        _intent_fragment_v5(intent, pools, created_pool_assets, context) for intent in intents
    )
    return _support_set_from_fragments_v5(fragments, context)


def derive_fcis_support_set_v5(
    *,
    intents: tuple[OwnedIntentV1, ...],
    pools: OwnedMapV1[str, CommittedPoolStateV1],
    context: FCISStepExecutionContextV1,
) -> FCISSupportSetV5:
    exact_intents = admit_intent_batch(intents)
    exact_pools = snapshot_pool_map(pools)
    context_result = admit_fcis_step_execution_context_v1(context)
    if (
        type(context_result) is not AdmitOk
        or type(context_result.value) is not FCISStepExecutionContextV1
    ):
        raise ValueError("support context admission rejected")
    return _derive_fcis_support_set_v5_admitted(
        intents=exact_intents,
        pools=exact_pools,
        context=context_result.value,
    )


def _sequential_read_trace_v5(
    state_read_trace: FCISStateReadTraceV5,
    context_read_trace: FCISContextReadTraceV5,
) -> FCISSequentialReadTraceV5:
    if type(state_read_trace) is not FCISStateReadTraceV5:
        raise TypeError("support root requires an exact state-read trace")
    if type(context_read_trace) is not FCISContextReadTraceV5:
        raise TypeError("support root requires an exact context-read trace")
    return FCISSequentialReadTraceV5(
        balance_keys=state_read_trace.balance_keys,
        pool_ids=state_read_trace.pool_ids,
        lp_keys=state_read_trace.lp_keys,
        nonce_keys=state_read_trace.nonce_keys,
        reads_fee_accumulator=state_read_trace.reads_fee_accumulator,
        context_paths=context_read_trace.paths,
    )


def support_contains_trace_v5(
    support: object,
    trace: object,
) -> bool:
    if type(support) is not FCISSupportSetV5 or type(trace) is not FCISSequentialReadTraceV5:
        return False
    return (
        set(trace.balance_keys).issubset(set(support.balance_keys))
        and set(trace.pool_ids).issubset(set(support.pool_ids))
        and set(trace.lp_keys).issubset(set(support.lp_keys))
        and set(trace.nonce_keys).issubset(set(support.nonce_keys))
        and (not trace.reads_fee_accumulator or support.include_fee_accumulator)
        and set(trace.context_paths).issubset(set(support.context_paths))
    )


def _encode_pair_keys_v5(
    keys: tuple[tuple[str, str], ...],
    sizes: tuple[int, int],
) -> bytes:
    out = bytearray(encode_uvarint(len(keys)))
    for left, right in keys:
        out += hex_to_bytes_fixed(left, nbytes=sizes[0], name="support key")
        out += hex_to_bytes_fixed(right, nbytes=sizes[1], name="support key")
    return bytes(out)


def _encode_string_keys_v5(keys: tuple[str, ...], size: int) -> bytes:
    out = bytearray(encode_uvarint(len(keys)))
    for key in keys:
        out += hex_to_bytes_fixed(key, nbytes=size, name="support key")
    return bytes(out)


def support_set_preimage_v5(support: FCISSupportSetV5) -> bytes:
    if type(support) is not FCISSupportSetV5:
        raise TypeError("support-set encoding requires an exact support set")
    sections = (
        (b"BAL", _encode_pair_keys_v5(support.balance_keys, (48, 32))),
        (b"POL", _encode_string_keys_v5(support.pool_ids, 32)),
        (b"LPK", _encode_pair_keys_v5(support.lp_keys, (48, 32))),
        (b"NNC", _encode_string_keys_v5(support.nonce_keys, 48)),
        (b"FEE", encode_uvarint(1 if support.include_fee_accumulator else 0)),
        (
            b"CTX",
            encode_uvarint(len(support.context_paths))
            + b"".join(encode_bytes(path.encode("utf-8")) for path in support.context_paths),
        ),
    )
    out = bytearray(domain_sep_bytes(FCIS_SUPPORT_SET_DOMAIN_V5, version=5))
    for label, section in sections:
        out += label
        out += encode_bytes(section)
    return bytes(out)


def _encode_balance_presence_v5(
    balances: CommittedBalanceTableV1,
    support: FCISSupportSetV5,
) -> bytes:
    index = dict(balances.entries)
    out = bytearray(encode_uvarint(len(support.balance_keys)))
    for pubkey, asset in support.balance_keys:
        out += hex_to_bytes_fixed(pubkey, nbytes=48, name="pubkey")
        out += hex_to_bytes_fixed(asset, nbytes=32, name="asset")
        value = index.get((pubkey, asset))
        out += encode_uvarint(0 if value is None else 1)
        if value is not None:
            out += encode_uvarint(value)
    return bytes(out)


def _encode_pool_presence_v5(
    pools: OwnedMapV1[str, CommittedPoolStateV1],
    support: FCISSupportSetV5,
) -> bytes:
    index = dict(pools.entries)
    out = bytearray(encode_uvarint(len(support.pool_ids)))
    for pool_id in support.pool_ids:
        out += hex_to_bytes_fixed(pool_id, nbytes=32, name="pool_id")
        pool = index.get(pool_id)
        out += encode_uvarint(0 if pool is None else 1)
        if pool is not None:
            out += _encode_pool_body_v1(pool)
    return bytes(out)


def _encode_optional_int_v5(value: int | None) -> bytes:
    if value is None:
        return encode_uvarint(0)
    return encode_uvarint(1) + encode_uvarint(value)


def _encode_lp_presence_v5(
    lp_balances: CommittedLPTableV1,
    support: FCISSupportSetV5,
) -> bytes:
    balance_index = dict(lp_balances.balance_entries)
    mint_index = dict(lp_balances.last_mint_entries)
    remove_index = dict(lp_balances.last_remove_entries)
    churn_index = dict(lp_balances.churn_tier_entries)
    churn_update_index = dict(lp_balances.last_churn_update_entries)
    out = bytearray(encode_uvarint(len(support.lp_keys)))
    for pubkey, pool_id in support.lp_keys:
        key = (pubkey, pool_id)
        out += hex_to_bytes_fixed(pubkey, nbytes=48, name="pubkey")
        out += hex_to_bytes_fixed(pool_id, nbytes=32, name="pool_id")
        out += _encode_optional_int_v5(balance_index.get(key))
        out += _encode_optional_int_v5(mint_index.get(key))
        out += _encode_optional_int_v5(remove_index.get(key))
        out += _encode_optional_int_v5(churn_index.get(key))
        out += _encode_optional_int_v5(churn_update_index.get(key))
    return bytes(out)


def _encode_nonce_presence_v5(
    nonces: CommittedNonceTableV1,
    support: FCISSupportSetV5,
) -> bytes:
    index = dict(nonces.entries)
    out = bytearray(encode_uvarint(len(support.nonce_keys)))
    for pubkey in support.nonce_keys:
        out += hex_to_bytes_fixed(pubkey, nbytes=48, name="pubkey")
        out += _encode_optional_int_v5(index.get(pubkey))
    return bytes(out)


def _encode_fee_presence_v5(
    fee_accumulator: CommittedFeeAccumulatorStateV1,
    support: FCISSupportSetV5,
) -> bytes:
    if not support.include_fee_accumulator:
        return encode_uvarint(0)
    return encode_uvarint(1) + encode_uvarint(fee_accumulator.dust)


def _command_preimage_v5(
    settlement: OwnedSettlementV1,
    intents: tuple[OwnedIntentV1, ...],
) -> bytes:
    out = bytearray(domain_sep_bytes(FCIS_SUPPORT_COMMAND_DOMAIN_V5, version=5))
    out += b"SET" + encode_bytes(_canonical_owned_settlement_bytes_admitted_v1(settlement))
    out += b"INT" + encode_uvarint(len(intents))
    for intent in intents:
        out += encode_bytes(_canonical_owned_intent_bytes_admitted_v1(intent))
    return bytes(out)


def _command_root_v5(
    settlement: OwnedSettlementV1,
    intents: tuple[OwnedIntentV1, ...],
) -> str:
    return sha256_hex(_command_preimage_v5(settlement, intents))


def _root_preimage_v5(
    *,
    command_root: str,
    context_hash: str,
    support_commitment: str,
    balances_section: bytes,
    pools_section: bytes,
    lp_section: bytes,
    nonce_section: bytes,
    fee_section: bytes,
) -> bytes:
    sections = (
        (b"CMD", hex_to_bytes_fixed(command_root, nbytes=32, name="command root")),
        (b"CTX", hex_to_bytes_fixed(context_hash, nbytes=32, name="context hash")),
        (b"SUP", hex_to_bytes_fixed(support_commitment, nbytes=32, name="support set")),
        (b"BAL", balances_section),
        (b"POL", pools_section),
        (b"LPS", lp_section),
        (b"NNC", nonce_section),
        (b"FEE", fee_section),
    )
    out = bytearray(domain_sep_bytes(FCIS_SUPPORT_ROOT_DOMAIN_V5, version=5))
    for label, section in sections:
        out += label
        out += encode_bytes(section)
    return bytes(out)


def _validate_support_command_context_v5(
    settlement: OwnedSettlementV1,
    intents: tuple[OwnedIntentV1, ...],
    context: FCISStepExecutionContextV1,
) -> None:
    if type(settlement) is not OwnedSettlementV1:
        raise TypeError("support root requires an exact settlement")
    if type(intents) is not tuple or any(type(item) is not OwnedIntentV1 for item in intents):
        raise TypeError("support root requires an exact intent tuple")
    if type(context) is not FCISStepExecutionContextV1:
        raise TypeError("support root requires an exact context")


def _validate_support_state_inputs_v5(
    balances: CommittedBalanceTableV1,
    pools: OwnedMapV1[str, CommittedPoolStateV1],
    lp_balances: CommittedLPTableV1,
    nonces: CommittedNonceTableV1,
    fee_accumulator: CommittedFeeAccumulatorStateV1,
) -> None:
    if type(balances) is not CommittedBalanceTableV1:
        raise TypeError("support root requires exact balances")
    if type(pools) is not OwnedMapV1:
        raise TypeError("support root requires an exact pool map")
    if type(lp_balances) is not CommittedLPTableV1:
        raise TypeError("support root requires exact LP state")
    if type(nonces) is not CommittedNonceTableV1:
        raise TypeError("support root requires exact nonces")
    if type(fee_accumulator) is not CommittedFeeAccumulatorStateV1:
        raise TypeError("support root requires an exact fee accumulator")


def _validate_support_trace_inputs_v5(
    state_read_trace: FCISStateReadTraceV5,
    context_read_trace: FCISContextReadTraceV5,
) -> None:
    if type(state_read_trace) is not FCISStateReadTraceV5:
        raise TypeError("support root requires an exact state-read trace")
    if type(context_read_trace) is not FCISContextReadTraceV5:
        raise TypeError("support root requires an exact context-read trace")


def _compute_fcis_support_root_v5_admitted(
    *,
    settlement: OwnedSettlementV1,
    intents: tuple[OwnedIntentV1, ...],
    context: FCISStepExecutionContextV1,
    balances: CommittedBalanceTableV1,
    pools: OwnedMapV1[str, CommittedPoolStateV1],
    lp_balances: CommittedLPTableV1,
    nonces: CommittedNonceTableV1,
    fee_accumulator: CommittedFeeAccumulatorStateV1,
    state_read_trace: FCISStateReadTraceV5,
    context_read_trace: FCISContextReadTraceV5,
) -> FCISSupportRootEvidenceV5:
    _validate_support_command_context_v5(settlement, intents, context)
    _validate_support_state_inputs_v5(
        balances,
        pools,
        lp_balances,
        nonces,
        fee_accumulator,
    )
    _validate_support_trace_inputs_v5(state_read_trace, context_read_trace)
    support = _derive_fcis_support_set_v5_admitted(
        intents=intents,
        pools=pools,
        context=context,
    )
    trace = _sequential_read_trace_v5(state_read_trace, context_read_trace)
    if not support_contains_trace_v5(support, trace):
        raise ValueError("sequential state or context reads escaped declared support")
    context_bytes = encode_fcis_execution_context_v1(FCIS_STEP_CONTEXT_SCHEMA_ID_V1, context)
    context_hash = sha256_hex(
        domain_sep_bytes(FCIS_SUPPORT_CONTEXT_HASH_DOMAIN_V1, version=1) + context_bytes
    )
    support_preimage = support_set_preimage_v5(support)
    support_commitment = sha256_hex(support_preimage)
    command_root = _command_root_v5(settlement, intents)
    root_preimage = _root_preimage_v5(
        command_root=command_root,
        context_hash=context_hash,
        support_commitment=support_commitment,
        balances_section=_encode_balance_presence_v5(balances, support),
        pools_section=_encode_pool_presence_v5(pools, support),
        lp_section=_encode_lp_presence_v5(lp_balances, support),
        nonce_section=_encode_nonce_presence_v5(nonces, support),
        fee_section=_encode_fee_presence_v5(fee_accumulator, support),
    )
    return FCISSupportRootEvidenceV5(
        support=support,
        trace=trace,
        support_set_preimage=support_preimage,
        support_set_commitment=support_commitment,
        command_root=command_root,
        execution_context_hash=context_hash,
        root_preimage=root_preimage,
        root=sha256_hex(root_preimage),
    )


def compute_fcis_support_root_v5(
    *,
    settlement: OwnedSettlementV1,
    intents: tuple[OwnedIntentV1, ...],
    context: FCISStepExecutionContextV1,
    balances: CommittedBalanceTableV1,
    pools: OwnedMapV1[str, CommittedPoolStateV1],
    lp_balances: CommittedLPTableV1,
    nonces: CommittedNonceTableV1,
    fee_accumulator: CommittedFeeAccumulatorStateV1,
    state_read_trace: FCISStateReadTraceV5,
    context_read_trace: FCISContextReadTraceV5,
) -> FCISSupportRootEvidenceV5:
    """Revalidate exact values and recompute one non-authoritative v5 proof."""

    if type(state_read_trace) is not FCISStateReadTraceV5:
        raise TypeError("support root requires an exact state-read trace")
    if type(context_read_trace) is not FCISContextReadTraceV5:
        raise TypeError("support root requires an exact context-read trace")
    exact_settlement = snapshot_settlement(settlement)
    exact_intents = admit_intent_batch(intents)
    context_result = admit_fcis_step_execution_context_v1(context)
    if (
        type(context_result) is not AdmitOk
        or type(context_result.value) is not FCISStepExecutionContextV1
    ):
        raise ValueError("support root context admission rejected")
    exact_trace = FCISStateReadTraceV5(
        balance_keys=state_read_trace.balance_keys,
        pool_ids=state_read_trace.pool_ids,
        lp_keys=state_read_trace.lp_keys,
        nonce_keys=state_read_trace.nonce_keys,
        reads_fee_accumulator=state_read_trace.reads_fee_accumulator,
    )
    exact_context_trace = FCISContextReadTraceV5(context_read_trace.paths)
    return _compute_fcis_support_root_v5_admitted(
        settlement=exact_settlement,
        intents=exact_intents,
        context=context_result.value,
        balances=snapshot_balance_table(balances),
        pools=snapshot_pool_map(pools),
        lp_balances=snapshot_lp_table(lp_balances),
        nonces=snapshot_nonce_table(nonces),
        fee_accumulator=snapshot_fee_accumulator(fee_accumulator),
        state_read_trace=exact_trace,
        context_read_trace=exact_context_trace,
    )


__all__ = (
    "FCIS_CONTEXT_SCHEMA_PATHS_V5",
    "FCIS_SUPPORT_COMMAND_ONLY_FIELDS_V5",
    "FCIS_SUPPORT_CONTEXT_PATHS_V5",
    "FCIS_SUPPORT_FIELD_DEPENDENCIES_V5",
    "FCIS_SUPPORT_INTENT_FIELD_INVENTORY_V5",
    "FCIS_SUPPORT_PROFILE_COMPLETE_V5",
    "FCIS_SUPPORT_PROFILE_ID_V5",
    "FCIS_SUPPORT_PROFILE_VERSION_V5",
    "FCISSequentialReadTraceV5",
    "FCISSupportRootEvidenceV5",
    "FCISSupportSetV5",
    "compute_fcis_support_root_v5",
    "derive_fcis_support_set_v5",
    "support_contains_trace_v5",
    "support_set_preimage_v5",
)
