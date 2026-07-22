"""Uniform-price batch clearing certificate verifier.

This module is intentionally narrow. UPBA supports one existing CPMM pool and
scoped exact-in / exact-out swap certificate policies. The verifier checks a
proposed uniform price certificate with deterministic integer arithmetic, then
constructs the canonical settlement implied by that certificate.
"""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from math import gcd
from typing import Any, Mapping, Sequence

from ..state.balances import AssetId, BalanceTable, PubKey
from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex
from ..state.immutable_collections import deep_thaw_json
from ..state.intents import Intent, IntentKind
from ..state.pools import CURVE_TAG_CPMM, PoolState, PoolStatus
from .cpmm import compute_fee_total
from .domain_limits import DEX_POOL_RESERVE_MAX, DEX_SWAP_AMOUNT_MAX
from .quote_receipts import pool_state_fingerprint
from .settlement import BalanceDelta, Fill, FillAction, ReserveDelta, Settlement

UNIFORM_BATCH_CERTIFICATE_SCHEMA_V1 = "zenodex/uniform_batch_clearing_certificate/v1"
UNIFORM_BATCH_CERTIFICATE_SCHEMA_V2 = "zenodex/uniform_batch_clearing_certificate/v2"
UNIFORM_BATCH_CERTIFICATE_SCHEMA_V3 = "zenodex/uniform_batch_clearing_certificate/v3"
UNIFORM_BATCH_CERTIFICATE_SCHEMA = UNIFORM_BATCH_CERTIFICATE_SCHEMA_V1
UNIFORM_BATCH_INTENT_SET_SCHEMA = "zenodex/uniform_batch_intent_set/v1"
UNIFORM_BATCH_POLICY_V1_ID = "zenodex/upba_v1/fixed_admission_full_fill_cpmm_exact_in"
UNIFORM_BATCH_POLICY_V2_ID = "zenodex/upba_v2/fixed_admission_partial_fill_cpmm_exact_in"
UNIFORM_BATCH_POLICY_V3_ID = "zenodex/upba_v3/fixed_admission_full_fill_cpmm_exact_out"
UNIFORM_BATCH_POLICY_ID = UNIFORM_BATCH_POLICY_V1_ID
UNIFORM_BATCH_PRICE_OBJECTIVE_ID = "zenodex/upba_v1/net_flow_ratio_or_pool_spot_price"
UNIFORM_BATCH_PRICE_RATIO_MAX = DEX_POOL_RESERVE_MAX
UNIFORM_BATCH_OUTPUT_AMOUNT_MAX = DEX_SWAP_AMOUNT_MAX * UNIFORM_BATCH_PRICE_RATIO_MAX
UNIFORM_BATCH_MAX_FILLS = 256
UNIFORM_BATCH_UNFILLED_REASON = "UNIFORM_BATCH_UNFILLED"
_BPS_DENOM = 10_000
_UNIFORM_BATCH_SUPPORTED_POLICY_IDS = frozenset(
    {UNIFORM_BATCH_POLICY_V1_ID, UNIFORM_BATCH_POLICY_V2_ID, UNIFORM_BATCH_POLICY_V3_ID}
)
_UNIFORM_BATCH_SCHEMA_BY_POLICY = {
    UNIFORM_BATCH_POLICY_V1_ID: UNIFORM_BATCH_CERTIFICATE_SCHEMA_V1,
    UNIFORM_BATCH_POLICY_V2_ID: UNIFORM_BATCH_CERTIFICATE_SCHEMA_V2,
    UNIFORM_BATCH_POLICY_V3_ID: UNIFORM_BATCH_CERTIFICATE_SCHEMA_V3,
}
_UNIFORM_BATCH_CERTIFICATE_KEYS = frozenset(
    {
        "schema",
        "policy_id",
        "price_objective_id",
        "pool_id",
        "base_asset",
        "quote_asset",
        "pool_state_hash",
        "intent_set_hash",
        "price_num",
        "price_den",
        "fills",
    }
)
_UNIFORM_BATCH_FILL_KEYS = frozenset({"intent_id", "executed_in", "executed_out"})


@dataclass(frozen=True)
class UniformBatchFillV1:
    intent_id: str
    executed_in: int
    executed_out: int

    def to_dict(self) -> dict[str, Any]:
        return {
            "intent_id": self.intent_id,
            "executed_in": int(self.executed_in),
            "executed_out": int(self.executed_out),
        }

    @classmethod
    def from_obj(cls, obj: Mapping[str, Any]) -> "UniformBatchFillV1":
        _reject_unknown_keys(obj, allowed=_UNIFORM_BATCH_FILL_KEYS, name="certificate.fill")
        return cls(
            intent_id=_require_str(obj.get("intent_id"), name="fill.intent_id"),
            executed_in=_require_nonnegative_int(
                obj.get("executed_in"),
                name="fill.executed_in",
                maximum=DEX_SWAP_AMOUNT_MAX,
            ),
            executed_out=_require_nonnegative_int(
                obj.get("executed_out"),
                name="fill.executed_out",
                maximum=UNIFORM_BATCH_OUTPUT_AMOUNT_MAX,
            ),
        )


@dataclass(frozen=True)
class UniformBatchCertificateV1:
    pool_id: str
    base_asset: str
    quote_asset: str
    pool_state_hash: str
    intent_set_hash: str
    price_num: int
    price_den: int
    fills: tuple[UniformBatchFillV1, ...]
    policy_id: str = UNIFORM_BATCH_POLICY_ID
    price_objective_id: str = UNIFORM_BATCH_PRICE_OBJECTIVE_ID
    schema: str = UNIFORM_BATCH_CERTIFICATE_SCHEMA

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "policy_id": self.policy_id,
            "price_objective_id": self.price_objective_id,
            "pool_id": self.pool_id,
            "base_asset": self.base_asset,
            "quote_asset": self.quote_asset,
            "pool_state_hash": self.pool_state_hash,
            "intent_set_hash": self.intent_set_hash,
            "price_num": int(self.price_num),
            "price_den": int(self.price_den),
            "fills": [fill.to_dict() for fill in self.fills],
        }

    @classmethod
    def from_obj(cls, obj: Mapping[str, Any]) -> "UniformBatchCertificateV1":
        _reject_unknown_keys(obj, allowed=_UNIFORM_BATCH_CERTIFICATE_KEYS, name="certificate")
        schema = _require_str(obj.get("schema"), name="certificate.schema")
        if schema not in (
            UNIFORM_BATCH_CERTIFICATE_SCHEMA_V1,
            UNIFORM_BATCH_CERTIFICATE_SCHEMA_V2,
            UNIFORM_BATCH_CERTIFICATE_SCHEMA_V3,
        ):
            raise ValueError("unsupported uniform batch certificate schema")
        policy_id = _require_str(obj.get("policy_id"), name="certificate.policy_id")
        if policy_id not in _UNIFORM_BATCH_SUPPORTED_POLICY_IDS:
            raise ValueError("unsupported uniform batch policy_id")
        expected_schema = _UNIFORM_BATCH_SCHEMA_BY_POLICY[policy_id]
        if schema != expected_schema:
            raise ValueError("uniform batch certificate schema does not match policy_id")
        price_objective_id = _require_str(
            obj.get("price_objective_id"),
            name="certificate.price_objective_id",
        )
        if price_objective_id != UNIFORM_BATCH_PRICE_OBJECTIVE_ID:
            raise ValueError("unsupported uniform batch price_objective_id")
        fills_obj = obj.get("fills")
        if not isinstance(fills_obj, Sequence) or isinstance(fills_obj, (str, bytes, bytearray)):
            raise TypeError("certificate.fills must be a sequence")
        if len(fills_obj) > UNIFORM_BATCH_MAX_FILLS:
            raise ValueError(f"certificate.fills exceeds maximum length {UNIFORM_BATCH_MAX_FILLS}")
        return cls(
            pool_id=_require_str(obj.get("pool_id"), name="certificate.pool_id"),
            base_asset=_require_str(obj.get("base_asset"), name="certificate.base_asset"),
            quote_asset=_require_str(obj.get("quote_asset"), name="certificate.quote_asset"),
            pool_state_hash=_require_str(
                obj.get("pool_state_hash"),
                name="certificate.pool_state_hash",
            ),
            intent_set_hash=_require_str(
                obj.get("intent_set_hash"),
                name="certificate.intent_set_hash",
            ),
            price_num=_require_positive_int(
                obj.get("price_num"),
                name="certificate.price_num",
                maximum=UNIFORM_BATCH_PRICE_RATIO_MAX,
            ),
            price_den=_require_positive_int(
                obj.get("price_den"),
                name="certificate.price_den",
                maximum=UNIFORM_BATCH_PRICE_RATIO_MAX,
            ),
            fills=tuple(UniformBatchFillV1.from_obj(_require_mapping(fill, name="certificate.fill")) for fill in fills_obj),
            policy_id=policy_id,
            price_objective_id=price_objective_id,
            schema=schema,
        )

    def hash(self) -> str:
        return uniform_batch_certificate_hash(self)


@dataclass(frozen=True)
class UniformBatchVerificationResult:
    ok: bool
    error: str | None
    settlement: Settlement | None = None
    certificate_hash: str | None = None


def uniform_batch_certificate_hash(certificate: UniformBatchCertificateV1 | Mapping[str, Any]) -> str:
    parsed = (
        certificate
        if isinstance(certificate, UniformBatchCertificateV1)
        else UniformBatchCertificateV1.from_obj(_require_mapping(certificate, name="certificate"))
    )
    _validate_certificate_shape(parsed)
    body = parsed.to_dict()
    hash_version = _uniform_batch_hash_version(parsed.schema)
    return sha256_hex(
        domain_sep_bytes("uniform_batch_clearing_certificate", version=hash_version)
        + canonical_json_bytes(body)
    )


def uniform_batch_pool_state_hash(pool: PoolState) -> str:
    return pool_state_fingerprint(pool)


def uniform_batch_intent_set_hash(intents: Sequence[Intent]) -> str:
    if len(intents) > UNIFORM_BATCH_MAX_FILLS:
        raise ValueError(f"uniform batch intent count exceeds maximum length {UNIFORM_BATCH_MAX_FILLS}")
    entries: list[dict[str, Any]] = []
    seen_ids: set[str] = set()
    for intent in intents:
        intent_id = _require_str(intent.intent_id, name="intent.intent_id")
        if intent_id in seen_ids:
            raise ValueError("duplicate intent_id")
        seen_ids.add(intent_id)
        fields = intent.fields if isinstance(intent.fields, Mapping) else {}
        if not isinstance(intent.kind, IntentKind):
            raise TypeError("intent.kind must be an IntentKind")
        entries.append(
            {
                "module": _require_str(intent.module, name="intent.module"),
                "version": _require_str(intent.version, name="intent.version"),
                "kind": intent.kind.value,
                "intent_id": intent_id,
                "sender_pubkey": _require_str(intent.sender_pubkey, name="intent.sender_pubkey"),
                "deadline": _require_nonnegative_int(intent.deadline, name="intent.deadline"),
                "salt": intent.salt,
                "fields": deep_thaw_json(fields),
            }
        )
    entries.sort(key=lambda entry: entry["intent_id"])
    body = {
        "schema": UNIFORM_BATCH_INTENT_SET_SCHEMA,
        "intents": entries,
    }
    return sha256_hex(
        domain_sep_bytes("uniform_batch_intent_set", version=1)
        + canonical_json_bytes(body)
    )


def build_uniform_batch_settlement_v1(
    *,
    intents: Sequence[Intent],
    pool: PoolState,
    balances: BalanceTable,
    certificate: UniformBatchCertificateV1 | Mapping[str, Any],
) -> Settlement:
    result = verify_uniform_batch_certificate_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        certificate=certificate,
    )
    if not result.ok or result.settlement is None:
        raise ValueError(result.error or "uniform batch certificate rejected")
    return result.settlement


def verify_uniform_batch_certificate_v1(
    *,
    intents: Sequence[Intent],
    pool: PoolState,
    balances: BalanceTable,
    certificate: UniformBatchCertificateV1 | Mapping[str, Any],
) -> UniformBatchVerificationResult:
    try:
        cert = certificate if isinstance(certificate, UniformBatchCertificateV1) else UniformBatchCertificateV1.from_obj(certificate)
        settlement = _build_uniform_batch_settlement_checked(
            intents=tuple(intents),
            pool=pool,
            balances=balances,
            certificate=cert,
        )
        return UniformBatchVerificationResult(
            ok=True,
            error=None,
            settlement=settlement,
            certificate_hash=cert.hash(),
        )
    except (TypeError, ValueError) as exc:
        return UniformBatchVerificationResult(ok=False, error=str(exc))


def validate_uniform_batch_settlement_v1(
    *,
    intents: Sequence[Intent],
    pool: PoolState,
    balances: BalanceTable,
    certificate: UniformBatchCertificateV1 | Mapping[str, Any],
    settlement: Settlement,
) -> tuple[bool, str | None]:
    result = verify_uniform_batch_certificate_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        certificate=certificate,
    )
    if not result.ok or result.settlement is None:
        return False, result.error
    if _settlement_fingerprint(settlement) != _settlement_fingerprint(result.settlement):
        return False, "uniform batch settlement mismatch"
    return True, None


def _build_uniform_batch_settlement_checked(
    *,
    intents: tuple[Intent, ...],
    pool: PoolState,
    balances: BalanceTable,
    certificate: UniformBatchCertificateV1,
) -> Settlement:
    _validate_certificate_shape(certificate)
    _validate_pool_scope(pool=pool, certificate=certificate)
    if not intents:
        raise ValueError("uniform batch requires at least one intent")
    if len(intents) > UNIFORM_BATCH_MAX_FILLS:
        raise ValueError(f"uniform batch intent count exceeds maximum length {UNIFORM_BATCH_MAX_FILLS}")
    expected_intent_set_hash = uniform_batch_intent_set_hash(intents)
    if certificate.intent_set_hash != expected_intent_set_hash:
        raise ValueError("certificate intent_set_hash mismatch")

    intents_by_id: dict[str, Intent] = {}
    for intent in intents:
        if intent.intent_id in intents_by_id:
            raise ValueError("duplicate intent_id")
        _validate_intent_scope(intent=intent, pool=pool, certificate=certificate)
        intents_by_id[intent.intent_id] = intent

    fill_ids = [fill.intent_id for fill in certificate.fills]
    if fill_ids != sorted(fill_ids):
        raise ValueError("certificate fills must be sorted by intent_id")
    if len(fill_ids) != len(set(fill_ids)):
        raise ValueError("duplicate certificate fill intent_id")
    expected_fill_ids = sorted(intents_by_id)
    if fill_ids != expected_fill_ids:
        raise ValueError("certificate must fill every admitted intent")
    objective_price_num, objective_price_den = _canonical_price_ratio(
        intents_by_id=intents_by_id,
        pool=pool,
        certificate=certificate,
    )
    if (certificate.price_num, certificate.price_den) != (objective_price_num, objective_price_den):
        raise ValueError("certificate price does not match canonical UPBA objective")

    balance_net: dict[tuple[PubKey, AssetId], int] = defaultdict(int)
    reserve_net: dict[AssetId, int] = defaultdict(int)
    fills: list[Fill] = []

    for cert_fill in certificate.fills:
        intent = intents_by_id.get(cert_fill.intent_id)
        if intent is None:
            raise ValueError("certificate fill references unknown intent_id")
        direction = _intent_direction(intent=intent, pool=pool)
        if certificate.policy_id in (UNIFORM_BATCH_POLICY_V1_ID, UNIFORM_BATCH_POLICY_V2_ID):
            amount_in = _require_positive_int(
                intent.get_field("amount_in"),
                name="intent.amount_in",
                maximum=DEX_SWAP_AMOUNT_MAX,
            )
            min_amount_out = _require_nonnegative_int(
                intent.get_field("min_amount_out"),
                name="intent.min_amount_out",
                maximum=UNIFORM_BATCH_OUTPUT_AMOUNT_MAX,
            )
            _validate_exact_in_fill_amount_for_policy(
                cert_fill=cert_fill,
                amount_in=amount_in,
                policy_id=certificate.policy_id,
            )
            if certificate.policy_id == UNIFORM_BATCH_POLICY_V1_ID and cert_fill.executed_in != amount_in:
                raise ValueError("certificate fill must consume full intent amount_in")
            if cert_fill.executed_in == 0:
                if cert_fill.executed_out != 0:
                    raise ValueError("unfilled certificate fill output must be zero")
                fills.append(
                    Fill(
                        intent_id=cert_fill.intent_id,
                        action=FillAction.REJECT,
                        reason=UNIFORM_BATCH_UNFILLED_REASON,
                    )
                )
                continue
            fee_paid = compute_fee_total(cert_fill.executed_in, pool.fee_bps)
            net_in = cert_fill.executed_in - fee_paid
            if net_in <= 0:
                raise ValueError("certificate fill net input is zero")
            expected_out = _uniform_price_out(
                net_in=net_in,
                direction=direction,
                price_num=certificate.price_num,
                price_den=certificate.price_den,
            )
            if cert_fill.executed_out != expected_out:
                raise ValueError("certificate fill output does not match uniform price")
            if cert_fill.executed_out * amount_in < min_amount_out * cert_fill.executed_in:
                raise ValueError("certificate fill violates intent limit price")
        elif certificate.policy_id == UNIFORM_BATCH_POLICY_V3_ID:
            amount_out = _require_positive_int(
                intent.get_field("amount_out"),
                name="intent.amount_out",
                maximum=DEX_SWAP_AMOUNT_MAX,
            )
            max_amount_in = _require_nonnegative_int(
                intent.get_field("max_amount_in"),
                name="intent.max_amount_in",
                maximum=DEX_SWAP_AMOUNT_MAX,
            )
            fee_paid = compute_fee_total(cert_fill.executed_in, pool.fee_bps)
            net_in = cert_fill.executed_in - fee_paid
            if net_in <= 0:
                raise ValueError("certificate fill net input is zero")
            if cert_fill.executed_out != amount_out:
                raise ValueError("certificate exact-out fill must match intent amount_out")
            if cert_fill.executed_in > max_amount_in:
                raise ValueError("certificate fill exceeds intent max_amount_in")
            expected_out = _uniform_price_out(
                net_in=net_in,
                direction=direction,
                price_num=certificate.price_num,
                price_den=certificate.price_den,
            )
            if expected_out < cert_fill.executed_out:
                raise ValueError("certificate exact-out input does not satisfy uniform price")
            expected_in = _uniform_price_exact_out_gross_in(
                amount_out=cert_fill.executed_out,
                direction=direction,
                price_num=certificate.price_num,
                price_den=certificate.price_den,
                fee_bps=pool.fee_bps,
            )
            if cert_fill.executed_in != expected_in:
                raise ValueError("certificate exact-out input is not minimal at uniform price")
        else:
            raise ValueError("unsupported uniform batch policy_id")

        sender = intent.sender_pubkey
        recipient = _require_str(intent.get_field("recipient", sender), name="intent.recipient")
        asset_in = str(intent.get_field("asset_in"))
        asset_out = str(intent.get_field("asset_out"))
        if balances.get(sender, asset_in) + balance_net[(sender, asset_in)] < cert_fill.executed_in:
            raise ValueError("insufficient balance for uniform fill")

        balance_net[(sender, asset_in)] -= cert_fill.executed_in
        balance_net[(recipient, asset_out)] += cert_fill.executed_out
        reserve_net[asset_in] += cert_fill.executed_in
        reserve_net[asset_out] -= cert_fill.executed_out
        fills.append(
            Fill(
                intent_id=cert_fill.intent_id,
                action=FillAction.FILL,
                amount_in_filled=cert_fill.executed_in,
                amount_out_filled=cert_fill.executed_out,
                fee_paid=fee_paid,
                reserve_in_before=pool.get_reserve(asset_in),
                reserve_out_before=pool.get_reserve(asset_out),
            )
        )

    reserve0_after = pool.reserve0 + reserve_net[pool.asset0]
    reserve1_after = pool.reserve1 + reserve_net[pool.asset1]
    if reserve0_after < 0 or reserve1_after < 0:
        raise ValueError("uniform batch would make pool reserves negative")
    if reserve0_after > DEX_POOL_RESERVE_MAX or reserve1_after > DEX_POOL_RESERVE_MAX:
        raise ValueError("uniform batch would exceed reserve domain")
    if reserve0_after * reserve1_after < pool.reserve0 * pool.reserve1:
        raise ValueError("uniform batch violates aggregate CPMM invariant")

    fills.sort(key=lambda fill: fill.intent_id)
    included_intents = [(fill.intent_id, fill.action) for fill in fills]
    balance_deltas = _net_to_balance_deltas(balance_net)
    reserve_deltas = _net_to_reserve_deltas(pool_id=pool.pool_id, reserve_net=reserve_net)
    certificate_hash = certificate.hash()
    return Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=included_intents,
        fills=fills,
        balance_deltas=balance_deltas,
        reserve_deltas=reserve_deltas,
        lp_deltas=[],
        events=[
            {
                "type": _uniform_batch_event_type(certificate.policy_id),
                "pool_id": pool.pool_id,
                "policy_id": certificate.policy_id,
                "price_objective_id": certificate.price_objective_id,
                "certificate_hash": certificate_hash,
            }
        ],
    )


def _validate_certificate_shape(certificate: UniformBatchCertificateV1) -> None:
    if certificate.schema not in (
        UNIFORM_BATCH_CERTIFICATE_SCHEMA_V1,
        UNIFORM_BATCH_CERTIFICATE_SCHEMA_V2,
        UNIFORM_BATCH_CERTIFICATE_SCHEMA_V3,
    ):
        raise ValueError("unsupported uniform batch certificate schema")
    if certificate.policy_id not in _UNIFORM_BATCH_SUPPORTED_POLICY_IDS:
        raise ValueError("unsupported uniform batch policy_id")
    expected_schema = _UNIFORM_BATCH_SCHEMA_BY_POLICY[certificate.policy_id]
    if certificate.schema != expected_schema:
        raise ValueError("uniform batch certificate schema does not match policy_id")
    if certificate.price_objective_id != UNIFORM_BATCH_PRICE_OBJECTIVE_ID:
        raise ValueError("unsupported uniform batch price_objective_id")
    _require_str(certificate.pool_id, name="certificate.pool_id")
    _require_str(certificate.base_asset, name="certificate.base_asset")
    _require_str(certificate.quote_asset, name="certificate.quote_asset")
    _require_str(certificate.pool_state_hash, name="certificate.pool_state_hash")
    _require_str(certificate.intent_set_hash, name="certificate.intent_set_hash")
    _require_positive_int(
        certificate.price_num,
        name="certificate.price_num",
        maximum=UNIFORM_BATCH_PRICE_RATIO_MAX,
    )
    _require_positive_int(
        certificate.price_den,
        name="certificate.price_den",
        maximum=UNIFORM_BATCH_PRICE_RATIO_MAX,
    )
    if gcd(int(certificate.price_num), int(certificate.price_den)) != 1:
        raise ValueError("certificate price ratio must be reduced")
    if not isinstance(certificate.fills, tuple):
        raise TypeError("certificate.fills must be a tuple")
    if len(certificate.fills) > UNIFORM_BATCH_MAX_FILLS:
        raise ValueError(f"certificate.fills exceeds maximum length {UNIFORM_BATCH_MAX_FILLS}")
    for fill in certificate.fills:
        if not isinstance(fill, UniformBatchFillV1):
            raise TypeError("certificate.fills must contain UniformBatchFillV1 values")
        _require_str(fill.intent_id, name="certificate.fill.intent_id")
        if certificate.policy_id in (UNIFORM_BATCH_POLICY_V1_ID, UNIFORM_BATCH_POLICY_V3_ID):
            _require_positive_int(
                fill.executed_in,
                name="certificate.fill.executed_in",
                maximum=DEX_SWAP_AMOUNT_MAX,
            )
            _require_positive_int(
                fill.executed_out,
                name="certificate.fill.executed_out",
                maximum=UNIFORM_BATCH_OUTPUT_AMOUNT_MAX,
            )
            continue
        _require_nonnegative_int(
            fill.executed_in,
            name="certificate.fill.executed_in",
            maximum=DEX_SWAP_AMOUNT_MAX,
        )
        _require_nonnegative_int(
            fill.executed_out,
            name="certificate.fill.executed_out",
            maximum=UNIFORM_BATCH_OUTPUT_AMOUNT_MAX,
        )


def _uniform_batch_event_type(policy_id: str) -> str:
    if policy_id == UNIFORM_BATCH_POLICY_V3_ID:
        return "UNIFORM_BATCH_CLEARING_V3"
    if policy_id == UNIFORM_BATCH_POLICY_V2_ID:
        return "UNIFORM_BATCH_CLEARING_V2"
    return "UNIFORM_BATCH_CLEARING_V1"


def _uniform_batch_hash_version(schema: str) -> int:
    if schema == UNIFORM_BATCH_CERTIFICATE_SCHEMA_V3:
        return 3
    if schema == UNIFORM_BATCH_CERTIFICATE_SCHEMA_V2:
        return 2
    return 1


def _validate_pool_scope(*, pool: PoolState, certificate: UniformBatchCertificateV1) -> None:
    if pool.pool_id != certificate.pool_id:
        raise ValueError("certificate pool_id mismatch")
    if uniform_batch_pool_state_hash(pool) != certificate.pool_state_hash:
        raise ValueError("certificate pool_state_hash mismatch")
    if pool.asset0 != certificate.base_asset or pool.asset1 != certificate.quote_asset:
        raise ValueError("certificate asset pair mismatch")
    if pool.status != PoolStatus.ACTIVE:
        raise ValueError("uniform batch pool must be active")
    if pool.curve_tag != CURVE_TAG_CPMM:
        raise ValueError("uniform batch v1 supports CPMM pools only")
    if pool.reserve0 <= 0 or pool.reserve1 <= 0:
        raise ValueError("uniform batch pool reserves must be positive")


def _validate_intent_scope(*, intent: Intent, pool: PoolState, certificate: UniformBatchCertificateV1) -> None:
    if certificate.policy_id == UNIFORM_BATCH_POLICY_V3_ID:
        if intent.kind != IntentKind.SWAP_EXACT_OUT:
            raise ValueError("uniform batch v3 supports SWAP_EXACT_OUT only")
    elif intent.kind != IntentKind.SWAP_EXACT_IN:
        raise ValueError("uniform batch v1/v2 supports SWAP_EXACT_IN only")
    if str(intent.get_field("pool_id")) != pool.pool_id:
        raise ValueError("uniform batch intent pool_id mismatch")
    asset_in = str(intent.get_field("asset_in"))
    asset_out = str(intent.get_field("asset_out"))
    if {asset_in, asset_out} != {certificate.base_asset, certificate.quote_asset}:
        raise ValueError("uniform batch intent asset pair mismatch")
    if asset_in == asset_out:
        raise ValueError("uniform batch intent assets must differ")
    _require_str(intent.sender_pubkey, name="intent.sender_pubkey")
    _require_str(intent.get_field("recipient", intent.sender_pubkey), name="intent.recipient")
    if certificate.policy_id == UNIFORM_BATCH_POLICY_V3_ID:
        _require_positive_int(intent.get_field("amount_out"), name="intent.amount_out", maximum=DEX_SWAP_AMOUNT_MAX)
        _require_nonnegative_int(
            intent.get_field("max_amount_in"),
            name="intent.max_amount_in",
            maximum=DEX_SWAP_AMOUNT_MAX,
        )
    else:
        _require_positive_int(intent.get_field("amount_in"), name="intent.amount_in", maximum=DEX_SWAP_AMOUNT_MAX)
        _require_nonnegative_int(
            intent.get_field("min_amount_out"),
            name="intent.min_amount_out",
            maximum=UNIFORM_BATCH_OUTPUT_AMOUNT_MAX,
        )


def _intent_direction(*, intent: Intent, pool: PoolState) -> str:
    asset_in = str(intent.get_field("asset_in"))
    asset_out = str(intent.get_field("asset_out"))
    if asset_in == pool.asset0 and asset_out == pool.asset1:
        return "base_to_quote"
    if asset_in == pool.asset1 and asset_out == pool.asset0:
        return "quote_to_base"
    raise ValueError("intent direction does not match pool assets")


def _validate_exact_in_fill_amount_for_policy(*, cert_fill: UniformBatchFillV1, amount_in: int, policy_id: str) -> None:
    if policy_id == UNIFORM_BATCH_POLICY_V1_ID:
        _require_positive_int(
            cert_fill.executed_in,
            name="certificate.fill.executed_in",
            maximum=DEX_SWAP_AMOUNT_MAX,
        )
        if cert_fill.executed_in != amount_in:
            raise ValueError("certificate fill must consume full intent amount_in")
        return
    if policy_id == UNIFORM_BATCH_POLICY_V2_ID:
        _require_nonnegative_int(
            cert_fill.executed_in,
            name="certificate.fill.executed_in",
            maximum=DEX_SWAP_AMOUNT_MAX,
        )
        if cert_fill.executed_in > amount_in:
            raise ValueError("certificate fill exceeds intent amount_in")
        return
    raise ValueError("unsupported uniform batch policy_id")


def _canonical_price_ratio(
    *,
    intents_by_id: Mapping[str, Intent],
    pool: PoolState,
    certificate: UniformBatchCertificateV1,
) -> tuple[int, int]:
    base_to_quote_net = 0
    quote_to_base_net = 0
    positive_fill_count = 0
    fills_by_id = {fill.intent_id: fill for fill in certificate.fills}
    for intent_id, intent in intents_by_id.items():
        fill = fills_by_id.get(intent_id)
        if fill is None:
            raise ValueError("certificate must fill every admitted intent")
        executed_in = _fill_executed_in_for_price_objective(
            intent=intent,
            fill=fill,
            policy_id=certificate.policy_id,
        )
        if executed_in == 0:
            continue
        positive_fill_count += 1
        fee_paid = compute_fee_total(executed_in, pool.fee_bps)
        net_in = executed_in - fee_paid
        if net_in <= 0:
            raise ValueError("certificate fill net input is zero")
        direction = _intent_direction(intent=intent, pool=pool)
        if direction == "base_to_quote":
            base_to_quote_net += net_in
        else:
            quote_to_base_net += net_in
    if certificate.policy_id == UNIFORM_BATCH_POLICY_V2_ID and positive_fill_count == 0:
        raise ValueError("uniform batch v2 requires at least one positive fill")
    if base_to_quote_net > 0 and quote_to_base_net > 0:
        return _reduce_ratio(quote_to_base_net, base_to_quote_net)
    return _reduce_ratio(pool.reserve1, pool.reserve0)


def _fill_executed_in_for_price_objective(
    *,
    intent: Intent,
    fill: UniformBatchFillV1,
    policy_id: str,
) -> int:
    if policy_id == UNIFORM_BATCH_POLICY_V1_ID:
        amount_in = _require_positive_int(
            intent.get_field("amount_in"),
            name="intent.amount_in",
            maximum=DEX_SWAP_AMOUNT_MAX,
        )
        _validate_exact_in_fill_amount_for_policy(cert_fill=fill, amount_in=amount_in, policy_id=policy_id)
        return amount_in
    if policy_id == UNIFORM_BATCH_POLICY_V2_ID:
        amount_in = _require_positive_int(
            intent.get_field("amount_in"),
            name="intent.amount_in",
            maximum=DEX_SWAP_AMOUNT_MAX,
        )
        _validate_exact_in_fill_amount_for_policy(cert_fill=fill, amount_in=amount_in, policy_id=policy_id)
        return fill.executed_in
    if policy_id == UNIFORM_BATCH_POLICY_V3_ID:
        if intent.kind != IntentKind.SWAP_EXACT_OUT:
            raise ValueError("uniform batch v3 supports SWAP_EXACT_OUT only")
        _require_positive_int(intent.get_field("amount_out"), name="intent.amount_out", maximum=DEX_SWAP_AMOUNT_MAX)
        _require_nonnegative_int(intent.get_field("max_amount_in"), name="intent.max_amount_in", maximum=DEX_SWAP_AMOUNT_MAX)
        _require_positive_int(fill.executed_in, name="certificate.fill.executed_in", maximum=DEX_SWAP_AMOUNT_MAX)
        _require_positive_int(fill.executed_out, name="certificate.fill.executed_out", maximum=UNIFORM_BATCH_OUTPUT_AMOUNT_MAX)
        return fill.executed_in
    raise ValueError("unsupported uniform batch policy_id")


def _reduce_ratio(numerator: int, denominator: int) -> tuple[int, int]:
    if numerator <= 0 or denominator <= 0:
        raise ValueError("canonical UPBA price ratio must be positive")
    divisor = gcd(int(numerator), int(denominator))
    return int(numerator) // divisor, int(denominator) // divisor


def _uniform_price_out(*, net_in: int, direction: str, price_num: int, price_den: int) -> int:
    if direction == "base_to_quote":
        return (net_in * price_num) // price_den
    if direction == "quote_to_base":
        return (net_in * price_den) // price_num
    raise ValueError("unsupported uniform batch direction")


def uniform_batch_exact_out_gross_in_for_price(
    *,
    amount_out: int,
    direction: str,
    price_num: int,
    price_den: int,
    fee_bps: int,
) -> int:
    parsed_amount_out = _require_positive_int(
        amount_out,
        name="amount_out",
        maximum=DEX_SWAP_AMOUNT_MAX,
    )
    parsed_price_num = _require_positive_int(
        price_num,
        name="price_num",
        maximum=UNIFORM_BATCH_PRICE_RATIO_MAX,
    )
    parsed_price_den = _require_positive_int(
        price_den,
        name="price_den",
        maximum=UNIFORM_BATCH_PRICE_RATIO_MAX,
    )
    parsed_fee_bps = _require_nonnegative_int(fee_bps, name="fee_bps", maximum=_BPS_DENOM)
    return _uniform_price_exact_out_gross_in(
        amount_out=parsed_amount_out,
        direction=direction,
        price_num=parsed_price_num,
        price_den=parsed_price_den,
        fee_bps=parsed_fee_bps,
    )


def _ceil_div_nonnegative(numerator: int, denominator: int) -> int:
    if numerator < 0:
        raise ValueError("numerator must be non-negative")
    if denominator <= 0:
        raise ValueError("denominator must be positive")
    return (numerator + denominator - 1) // denominator


def _uniform_price_exact_out_gross_in(
    *,
    amount_out: int,
    direction: str,
    price_num: int,
    price_den: int,
    fee_bps: int,
) -> int:
    if fee_bps >= _BPS_DENOM:
        raise ValueError("cannot compute exact-out uniform batch input with 100% fee")
    if direction == "base_to_quote":
        required_net = _ceil_div_nonnegative(amount_out * price_den, price_num)
    elif direction == "quote_to_base":
        required_net = _ceil_div_nonnegative(amount_out * price_num, price_den)
    else:
        raise ValueError("unsupported uniform batch direction")
    return _ceil_div_nonnegative(required_net * _BPS_DENOM, _BPS_DENOM - fee_bps)


def _net_to_balance_deltas(balance_net: Mapping[tuple[PubKey, AssetId], int]) -> list[BalanceDelta]:
    out: list[BalanceDelta] = []
    for (pubkey, asset), net in sorted(balance_net.items()):
        if net == 0:
            continue
        out.append(
            BalanceDelta(
                pubkey=pubkey,
                asset=asset,
                delta_add=max(net, 0),
                delta_sub=max(-net, 0),
            )
        )
    return out


def _net_to_reserve_deltas(*, pool_id: str, reserve_net: Mapping[AssetId, int]) -> list[ReserveDelta]:
    out: list[ReserveDelta] = []
    for asset, net in sorted(reserve_net.items()):
        if net == 0:
            continue
        out.append(
            ReserveDelta(
                pool_id=pool_id,
                asset=asset,
                delta_add=max(net, 0),
                delta_sub=max(-net, 0),
            )
        )
    return out


def _settlement_fingerprint(settlement: Settlement) -> dict[str, Any]:
    return {
        "module": settlement.module,
        "version": settlement.version,
        "included_intents": [(intent_id, action.value) for intent_id, action in settlement.included_intents],
        "fills": [
            {
                "intent_id": fill.intent_id,
                "action": fill.action.value,
                "reason": fill.reason,
                "amount_in_filled": fill.amount_in_filled,
                "amount_out_filled": fill.amount_out_filled,
                "fee_paid": fill.fee_paid,
                "reserve_in_before": fill.reserve_in_before,
                "reserve_out_before": fill.reserve_out_before,
            }
            for fill in settlement.fills
        ],
        "balance_deltas": [
            {
                "pubkey": delta.pubkey,
                "asset": delta.asset,
                "delta_add": delta.delta_add,
                "delta_sub": delta.delta_sub,
            }
            for delta in settlement.balance_deltas
        ],
        "reserve_deltas": [
            {
                "pool_id": delta.pool_id,
                "asset": delta.asset,
                "delta_add": delta.delta_add,
                "delta_sub": delta.delta_sub,
            }
            for delta in settlement.reserve_deltas
        ],
        "lp_deltas": [
            {
                "pubkey": delta.pubkey,
                "pool_id": delta.pool_id,
                "delta_add": delta.delta_add,
                "delta_sub": delta.delta_sub,
            }
            for delta in settlement.lp_deltas
        ],
        "events": settlement.events or [],
    }


def _require_mapping(value: Any, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be an object")
    return value


def _reject_unknown_keys(value: Mapping[str, Any], *, allowed: frozenset[str], name: str) -> None:
    unknown = sorted(set(value) - set(allowed))
    if unknown:
        joined = ", ".join(unknown)
        raise ValueError(f"{name} contains unsupported keys: {joined}")


def _require_str(value: Any, *, name: str) -> str:
    if not isinstance(value, str) or not value:
        raise TypeError(f"{name} must be a non-empty string")
    return str(value)


def _require_nonnegative_int(value: Any, *, name: str, maximum: int | None = None) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    if value < 0:
        raise ValueError(f"{name} must be non-negative")
    if maximum is not None and value > maximum:
        raise ValueError(f"{name} exceeds maximum")
    return int(value)


def _require_positive_int(value: Any, *, name: str, maximum: int | None = None) -> int:
    value_int = _require_nonnegative_int(value, name=name, maximum=maximum)
    if value_int <= 0:
        raise ValueError(f"{name} must be positive")
    return value_int
