"""
Perpetuals module state (protocol-level, snapshot-friendly).

This file defines the *persistent* perps state that lives inside `DexState` and is
encoded/decoded by `src/integration/dex_snapshot.py`.

The actual risk-engine step logic is implemented separately (see
`src/core/perp_epoch.py` + `src/kernels/dex/perp_epoch_isolated_v3.yaml`).

Units note:
- Isolated markets (`kind="isolated_v2"`) track collateral in *quote units* (`collateral_quote`).
- Clearinghouse markets (`kind="clearinghouse_2p_v1"`) track quote amounts in *quote-e8*
  (`collateral_e8_*`, `fee_pool_e8`, `net_deposited_e8`) so epoch PnL updates are exact integers
  (no division / rounding dust).
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Literal

from ..state.canonical import canonical_hex_fixed_allow_0x
from . import perps_fixed_validation as _fixed_validation
from . import perps_isolated_validation as _isolated_validation
from . import perps_np_validation as _np_validation
from .perp_apply_funding_auto_gate import (
    MARK_PRICE_SOURCE_EXTERNAL_MEDIAN,
)
from .perps_fixed_validation import (
    FixedClearinghouseValidationRequest,
    validate_fixed_clearinghouse_shape,
    validate_three_party_transfer_clearinghouse_invariants,
    validate_two_party_clearinghouse_invariants,
)
from .perps_isolated_validation import (
    validate_isolated_account_state,
    validate_isolated_state_consistency,
)
from .perps_np_validation import (
    NpMarketValidationRequest,
    validate_np_account_record,
    validate_np_market_state,
    validate_np_pending_intent_record,
)

# Kernel value domain (mirrors the YAML spec / generated refs): bool | int | str
Value = bool | int | str

MAX_PENDING_FUNDING_CLOSEOUT_ROOT_HASHES = 64
MAX_FUNDING_CLOSEOUT_SINK_CLAIMANT_BALANCES = 128
MAX_FUNDING_CLOSEOUT_RECEIVER_CLAIM_BALANCES = 128
MAX_FUNDING_CLOSEOUT_RECEIVER_CLAIM_LOTS = 256
FUNDING_CLOSEOUT_RECEIVER_CLAIM_NO_EXPIRY_EPOCH = 2**63 - 1


PERPS_STATE_VERSION_V4 = 4
PERPS_STATE_VERSION_V5 = 5
PERPS_STATE_VERSION = PERPS_STATE_VERSION_V5


def _pubkey_bytes48(pubkey: str, *, name: str) -> bytes:
    canon = canonical_hex_fixed_allow_0x(pubkey, nbytes=48, name=name)
    return bytes.fromhex(canon[2:])


def _pubkey_bytes48_or_none(pubkey: str) -> bytes | None:
    try:
        return _pubkey_bytes48(pubkey, name="pubkey")
    except (TypeError, ValueError):
        return None


def _is_non_bool_int(value: object) -> bool:
    return isinstance(value, int) and not isinstance(value, bool)


def _is_zero_one_int(value: object) -> bool:
    return _is_non_bool_int(value) and value in (0, 1)


def _is_non_empty_str(value: object) -> bool:
    return isinstance(value, str) and bool(value)


def _is_sha256_hash(value: object) -> bool:
    if not isinstance(value, str):
        return False
    if not value.startswith("sha256:") or len(value) != len("sha256:") + 64:
        return False
    suffix = value[len("sha256:") :]
    return suffix.lower() == suffix and all(ch in "0123456789abcdef" for ch in suffix)


def _normalize_pending_funding_closeout_root_hashes(value: object) -> tuple[str, ...]:
    if value is None:
        return ()
    if not isinstance(value, tuple):
        raise TypeError("pending_funding_closeout_root_hashes must be a tuple")
    if len(value) > MAX_PENDING_FUNDING_CLOSEOUT_ROOT_HASHES:
        raise ValueError("too many pending funding closeout root hashes")
    roots: list[str] = []
    for root_hash in value:
        if not _is_sha256_hash(root_hash):
            raise ValueError(
                "pending funding closeout root hash must be sha256:<64 lowercase hex chars>"
            )
        roots.append(str(root_hash))
    return tuple(sorted(set(roots)))


def _normalize_pending_funding_closeout_source_availability_hashes(
    value: object,
) -> tuple[str, ...]:
    if value is None:
        return ()
    if not isinstance(value, tuple):
        raise TypeError("pending_funding_closeout_source_availability_hashes must be a tuple")
    if len(value) > MAX_PENDING_FUNDING_CLOSEOUT_ROOT_HASHES:
        raise ValueError("too many pending funding closeout source availability hashes")
    roots: list[str] = []
    for root_hash in value:
        if not _is_sha256_hash(root_hash):
            raise ValueError(
                "pending funding closeout source availability hash must be sha256:<64 lowercase hex chars>"
            )
        roots.append(str(root_hash))
    return tuple(sorted(set(roots)))


def _normalize_pending_funding_closeout_carried_liability_hashes(
    value: object,
) -> tuple[str, ...]:
    if value is None:
        return ()
    if not isinstance(value, tuple):
        raise TypeError("pending_funding_closeout_carried_liability_hashes must be a tuple")
    if len(value) > MAX_PENDING_FUNDING_CLOSEOUT_ROOT_HASHES:
        raise ValueError("too many pending funding closeout carried liability hashes")
    roots: list[str] = []
    for root_hash in value:
        if not _is_sha256_hash(root_hash):
            raise ValueError(
                "pending funding closeout carried liability hash must be sha256:<64 lowercase hex chars>"
            )
        roots.append(str(root_hash))
    return tuple(sorted(set(roots)))


def _normalize_funding_closeout_policy_ledger_hashes(
    value: object,
) -> tuple[str, ...]:
    if value is None:
        return ()
    if not isinstance(value, tuple):
        raise TypeError("funding_closeout_policy_ledger_hashes must be a tuple")
    if len(value) > MAX_PENDING_FUNDING_CLOSEOUT_ROOT_HASHES:
        raise ValueError("too many funding closeout policy ledger hashes")
    roots: list[str] = []
    for root_hash in value:
        if not _is_sha256_hash(root_hash):
            raise ValueError(
                "funding closeout policy ledger hash must be sha256:<64 lowercase hex chars>"
            )
        roots.append(str(root_hash))
    return tuple(sorted(set(roots)))


def _normalize_funding_closeout_sink_claimant_balances(
    value: object,
) -> tuple[tuple[str, int], ...]:
    if value is None:
        return ()
    if not isinstance(value, tuple):
        raise TypeError("funding_closeout_sink_claimant_balances_quote must be a tuple")
    if len(value) > MAX_FUNDING_CLOSEOUT_SINK_CLAIMANT_BALANCES:
        raise ValueError("too many funding closeout sink claimant balances")
    balances: list[tuple[str, int]] = []
    seen: set[str] = set()
    for row in value:
        if not isinstance(row, tuple) or len(row) != 2:
            raise TypeError("funding closeout sink claimant balance row must be a pair")
        claimant, balance_quote = row
        if not _is_non_empty_str(claimant):
            raise TypeError("funding closeout sink claimant must be a non-empty string")
        if len(str(claimant)) > 256:
            raise ValueError("funding closeout sink claimant too large")
        if claimant in seen:
            raise ValueError("duplicate funding closeout sink claimant balance")
        if not _is_non_bool_int(balance_quote):
            raise TypeError("funding closeout sink claimant balance must be an int")
        if int(balance_quote) <= 0:
            raise ValueError("funding closeout sink claimant balance must be positive")
        seen.add(str(claimant))
        balances.append((str(claimant), int(balance_quote)))
    return tuple(sorted(balances, key=lambda item: item[0]))


def _normalize_funding_closeout_receiver_claim_balances(
    value: object,
) -> tuple[tuple[str, int], ...]:
    if value is None:
        return ()
    if not isinstance(value, tuple):
        raise TypeError("funding_closeout_receiver_claim_balances_quote must be a tuple")
    if len(value) > MAX_FUNDING_CLOSEOUT_RECEIVER_CLAIM_BALANCES:
        raise ValueError("too many funding closeout receiver claim balances")
    balances: list[tuple[str, int]] = []
    seen: set[str] = set()
    for row in value:
        if not isinstance(row, tuple) or len(row) != 2:
            raise TypeError("funding closeout receiver claim balance row must be a pair")
        account_pubkey, balance_quote = row
        if not _is_non_empty_str(account_pubkey):
            raise TypeError("funding closeout receiver claim account must be a non-empty string")
        if len(str(account_pubkey)) > 512:
            raise ValueError("funding closeout receiver claim account too large")
        if account_pubkey in seen:
            raise ValueError("duplicate funding closeout receiver claim balance")
        if not _is_non_bool_int(balance_quote):
            raise TypeError("funding closeout receiver claim balance must be an int")
        if int(balance_quote) <= 0:
            raise ValueError("funding closeout receiver claim balance must be positive")
        seen.add(str(account_pubkey))
        balances.append((str(account_pubkey), int(balance_quote)))
    return tuple(sorted(balances, key=lambda item: item[0]))


def _normalize_funding_closeout_receiver_claim_lots(
    value: object,
) -> tuple[tuple[str, str, int, int], ...]:
    if value is None:
        return ()
    if not isinstance(value, tuple):
        raise TypeError("funding_closeout_receiver_claim_lots_quote must be a tuple")
    if len(value) > MAX_FUNDING_CLOSEOUT_RECEIVER_CLAIM_LOTS:
        raise ValueError("too many funding closeout receiver claim lots")
    lots: list[tuple[str, str, int, int]] = []
    seen: set[tuple[str, str]] = set()
    for row in value:
        if not isinstance(row, tuple) or len(row) != 4:
            raise TypeError("funding closeout receiver claim lot row must be a 4-tuple")
        account_pubkey, lot_id, balance_quote, expires_at_epoch = row
        if not _is_non_empty_str(account_pubkey):
            raise TypeError(
                "funding closeout receiver claim lot account must be a non-empty string"
            )
        if len(str(account_pubkey)) > 512:
            raise ValueError("funding closeout receiver claim lot account too large")
        if not _is_non_empty_str(lot_id):
            raise TypeError("funding closeout receiver claim lot_id must be a non-empty string")
        if len(str(lot_id)) > 256:
            raise ValueError("funding closeout receiver claim lot_id too large")
        key = (str(account_pubkey), str(lot_id))
        if key in seen:
            raise ValueError("duplicate funding closeout receiver claim lot")
        if not _is_non_bool_int(balance_quote):
            raise TypeError("funding closeout receiver claim lot balance must be an int")
        if int(balance_quote) <= 0:
            raise ValueError("funding closeout receiver claim lot balance must be positive")
        if not _is_non_bool_int(expires_at_epoch):
            raise TypeError("funding closeout receiver claim lot expiry must be an int")
        if int(expires_at_epoch) < 0:
            raise ValueError("funding closeout receiver claim lot expiry must be non-negative")
        seen.add(key)
        lots.append(
            (
                str(account_pubkey),
                str(lot_id),
                int(balance_quote),
                int(expires_at_epoch),
            )
        )
    return tuple(sorted(lots, key=lambda item: (item[0], item[3], item[1])))


def funding_closeout_receiver_claim_balances_from_lots(
    lots: tuple[tuple[str, str, int, int], ...],
) -> tuple[tuple[str, int], ...]:
    balances: dict[str, int] = {}
    for account_pubkey, _lot_id, balance_quote, _expires_at_epoch in lots:
        balances[str(account_pubkey)] = int(balances.get(str(account_pubkey), 0)) + int(
            balance_quote
        )
    if len(balances) > MAX_FUNDING_CLOSEOUT_RECEIVER_CLAIM_BALANCES:
        raise ValueError("too many funding closeout receiver claim balance accounts")
    return tuple(sorted((key, value) for key, value in balances.items() if value > 0))


def _infer_epoch_phase(gs: dict) -> int:
    """Infer epoch_phase from existing global_state fields for legacy snapshots.

    Epoch lifecycle: advance_epoch→Open, publish_clearing_price→PricePublished,
    settle_epoch→Settled. We detect the phase from the side-effects each
    transition leaves:
      - PricePublished: clearing_price_seen=True, clearing_price_epoch==now_epoch
      - Settled: additionally oracle_last_update_epoch==now_epoch, oracle_seen=True
      - Open: otherwise (no clearing price published in the current epoch)
    """
    now = _legacy_global_int(gs, "now_epoch", 0)
    cp_seen = _legacy_global_bool(gs, "clearing_price_seen", False)
    cp_epoch = _legacy_global_int(gs, "clearing_price_epoch", -1)
    o_seen = _legacy_global_bool(gs, "oracle_seen", False)
    o_epoch = _legacy_global_int(gs, "oracle_last_update_epoch", -1)

    # Canonical kernel encoding: Open=0, PricePublished=1, Settled=2.
    if cp_seen and cp_epoch == now:
        if o_seen and o_epoch == now:
            return 2
        return 1
    return 0


def _legacy_global_int(gs: dict, key: str, default: int) -> int:
    value = gs.get(key, default)
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError(f"global_state[{key!r}] must be an int")
    return int(value)


def _legacy_global_bool(gs: dict, key: str, default: bool) -> bool:
    value = gs.get(key, default)
    if isinstance(value, bool):
        return bool(value)
    if isinstance(value, int) and value in (0, 1):
        return bool(value)
    raise TypeError(f"global_state[{key!r}] must be a bool or 0/1 int")


def _validate_isolated_market_header(
    *,
    kind: str,
    quote_asset: str,
    global_state: object,
    accounts: object,
) -> None:
    if kind != PERP_MARKET_KIND_ISOLATED_V2:
        raise ValueError(f"unsupported perps market kind: {kind}")
    if not _is_non_empty_str(quote_asset):
        raise TypeError("quote_asset must be a non-empty string")
    if not isinstance(global_state, dict):
        raise TypeError("global_state must be a dict")
    if not isinstance(accounts, dict):
        raise TypeError("accounts must be a dict")


def _ensure_isolated_global_defaults(global_state: Dict[str, Value]) -> None:
    # Backward compat: infer epoch_phase from existing state for legacy snapshots.
    if "epoch_phase" not in global_state:
        global_state["epoch_phase"] = _infer_epoch_phase(global_state)
    if "mark_price_source_kind" not in global_state:
        global_state["mark_price_source_kind"] = MARK_PRICE_SOURCE_EXTERNAL_MEDIAN


def _validate_isolated_global_keys(global_state: Dict[str, Value]) -> None:
    keys = set(global_state.keys())
    extra = keys - PERP_ISOLATED_GLOBAL_KEYS
    missing = PERP_ISOLATED_GLOBAL_KEYS - keys
    if extra:
        raise ValueError(f"global_state has unknown keys: {sorted(extra)[:8]}")
    if missing:
        raise ValueError(f"global_state missing required keys: {sorted(missing)[:8]}")


def _normalize_isolated_epoch_phase(global_state: Dict[str, Value]) -> None:
    # Canonical kernel encoding: Open=0, PricePublished=1, Settled=2.
    ep = global_state.get("epoch_phase")
    if isinstance(ep, str):
        if ep not in _EPOCH_PHASE_STR_TO_INT:
            raise ValueError(f"global_state['epoch_phase'] invalid: {ep!r}")
        global_state["epoch_phase"] = _EPOCH_PHASE_STR_TO_INT[ep]
        return
    if _is_non_bool_int(ep):
        if ep not in _EPOCH_PHASE_INT_TO_STR:
            raise ValueError(f"global_state['epoch_phase'] int value {ep} out of range [0,2]")
        return
    raise TypeError("global_state['epoch_phase'] must be a str or int")


def _validate_normalized_isolated_epoch_phase(value: Value) -> None:
    if not _is_non_bool_int(value) or value not in _EPOCH_PHASE_INT_TO_STR:
        raise ValueError(f"global_state['epoch_phase'] invalid: {value!r}")


def _normalize_isolated_bool_global_value(
    global_state: Dict[str, Value], key: str, value: Value
) -> None:
    if isinstance(value, bool):
        return
    if _is_zero_one_int(value):
        global_state[key] = bool(value)
        return
    raise TypeError(f"global_state[{key!r}] must be a bool (or 0/1 int)")


def _normalize_isolated_global_value(
    global_state: Dict[str, Value], key: str, value: Value
) -> None:
    if key == "epoch_phase":
        _validate_normalized_isolated_epoch_phase(value)
        return

    if key in _PERP_ISOLATED_GLOBAL_BOOL_KEYS:
        # Some upstreams historically used 0/1 ints for booleans; normalize.
        _normalize_isolated_bool_global_value(global_state, key, value)
        return

    if _is_non_bool_int(value):
        return
    raise TypeError(f"global_state[{key!r}] must be an int")


def _normalize_isolated_global_values(global_state: Dict[str, Value]) -> None:
    for key, value in list(global_state.items()):
        _normalize_isolated_global_value(global_state, key, value)


_EPOCH_PHASE_STR_TO_INT: dict[str, int] = {"Open": 0, "PricePublished": 1, "Settled": 2}
_EPOCH_PHASE_INT_TO_STR: dict[int, str] = {0: "Open", 1: "PricePublished", 2: "Settled"}

PERP_MARKET_KIND_ISOLATED_V2: Literal["isolated_v2"] = "isolated_v2"
PERP_MARKET_KIND_CLEARINGHOUSE_2P_V1: Literal["clearinghouse_2p_v1"] = "clearinghouse_2p_v1"
PERP_MARKET_KIND_CLEARINGHOUSE_3P_TRANSFER_V1: Literal["clearinghouse_3p_transfer_v1"] = (
    "clearinghouse_3p_transfer_v1"
)
# Open, dynamic-membership N-party net-zero clearinghouse (3+ independent wallets).
# Unlike the fixed-slot 2p/3p kernels this market has no a/b/c slots. It holds a
# dynamic account set and delegates transition semantics to
# `src/core/perp_np_clearinghouse.py`.
PERP_MARKET_KIND_CLEARINGHOUSE_NP_V1: Literal["clearinghouse_np_v1"] = "clearinghouse_np_v1"

# Compatibility re-exports: existing snapshot and integration code import these
# constants from `src.core.perps`.
PERP_ACCOUNT_KEYS = _isolated_validation.PERP_ACCOUNT_KEYS
PERP_ISOLATED_GLOBAL_KEYS = _isolated_validation.PERP_ISOLATED_GLOBAL_KEYS
_PERP_ISOLATED_GLOBAL_BOOL_KEYS = _isolated_validation.PERP_ISOLATED_GLOBAL_BOOL_KEYS
PERP_CLEARINGHOUSE_NP_ACCOUNT_KEYS = _np_validation.PERP_CLEARINGHOUSE_NP_ACCOUNT_KEYS
PERP_CLEARINGHOUSE_NP_GLOBAL_KEYS = _np_validation.PERP_CLEARINGHOUSE_NP_GLOBAL_KEYS
PERP_CLEARINGHOUSE_NP_PENDING_INTENT_KEYS = _np_validation.PERP_CLEARINGHOUSE_NP_PENDING_INTENT_KEYS
PERP_CLEARINGHOUSE_2P_BOOL_KEYS = _fixed_validation.PERP_CLEARINGHOUSE_2P_BOOL_KEYS
PERP_CLEARINGHOUSE_2P_STATE_KEYS = _fixed_validation.PERP_CLEARINGHOUSE_2P_STATE_KEYS
PERP_CLEARINGHOUSE_3P_TRANSFER_BOOL_KEYS = (
    _fixed_validation.PERP_CLEARINGHOUSE_3P_TRANSFER_BOOL_KEYS
)
PERP_CLEARINGHOUSE_3P_TRANSFER_STATE_KEYS = (
    _fixed_validation.PERP_CLEARINGHOUSE_3P_TRANSFER_STATE_KEYS
)

# Backwards-compatible alias (older modules import PERP_GLOBAL_KEYS).
PERP_GLOBAL_KEYS: set[str] = PERP_ISOLATED_GLOBAL_KEYS


@dataclass(frozen=True)
class PerpAccountState:
    """Per-account isolated margin state for the epoch-perp kernel (v2 default)."""

    position_base: int
    entry_price_e8: int
    collateral_quote: int
    funding_paid_cumulative: int
    funding_last_applied_epoch: int
    liquidated_this_step: bool

    def __post_init__(self) -> None:
        validate_isolated_account_state(self)

    def to_kernel_state(self) -> dict[str, Value]:
        return {
            "position_base": int(self.position_base),
            "entry_price_e8": int(self.entry_price_e8),
            "collateral_quote": int(self.collateral_quote),
            "funding_paid_cumulative": int(self.funding_paid_cumulative),
            "funding_last_applied_epoch": int(self.funding_last_applied_epoch),
            "liquidated_this_step": bool(self.liquidated_this_step),
        }


@dataclass(frozen=True)
class PerpMarketState:
    """Single-market state: global epoch/oracle + account table."""

    quote_asset: str
    global_state: Dict[str, Value]
    accounts: Dict[str, PerpAccountState]
    kind: Literal["isolated_v2"] = PERP_MARKET_KIND_ISOLATED_V2
    pending_funding_closeout_root_hashes: tuple[str, ...] = ()
    pending_funding_closeout_source_availability_hashes: tuple[str, ...] = ()
    pending_funding_closeout_carried_liability_hashes: tuple[str, ...] = ()
    funding_closeout_policy_ledger_hashes: tuple[str, ...] = ()
    funding_closeout_sink_claimant_balances_quote: tuple[tuple[str, int], ...] = ()
    funding_closeout_receiver_claim_balances_quote: tuple[tuple[str, int], ...] = ()
    funding_closeout_receiver_claim_lots_quote: tuple[tuple[str, str, int, int], ...] = ()

    def __post_init__(self) -> None:
        _validate_isolated_market_header(
            kind=self.kind,
            quote_asset=self.quote_asset,
            global_state=self.global_state,
            accounts=self.accounts,
        )
        _ensure_isolated_global_defaults(self.global_state)
        _validate_isolated_global_keys(self.global_state)
        _normalize_isolated_epoch_phase(self.global_state)
        _normalize_isolated_global_values(self.global_state)
        object.__setattr__(
            self,
            "pending_funding_closeout_root_hashes",
            _normalize_pending_funding_closeout_root_hashes(
                self.pending_funding_closeout_root_hashes,
            ),
        )
        object.__setattr__(
            self,
            "pending_funding_closeout_source_availability_hashes",
            _normalize_pending_funding_closeout_source_availability_hashes(
                self.pending_funding_closeout_source_availability_hashes,
            ),
        )
        object.__setattr__(
            self,
            "pending_funding_closeout_carried_liability_hashes",
            _normalize_pending_funding_closeout_carried_liability_hashes(
                self.pending_funding_closeout_carried_liability_hashes,
            ),
        )
        object.__setattr__(
            self,
            "funding_closeout_policy_ledger_hashes",
            _normalize_funding_closeout_policy_ledger_hashes(
                self.funding_closeout_policy_ledger_hashes,
            ),
        )
        object.__setattr__(
            self,
            "funding_closeout_sink_claimant_balances_quote",
            _normalize_funding_closeout_sink_claimant_balances(
                self.funding_closeout_sink_claimant_balances_quote,
            ),
        )
        object.__setattr__(
            self,
            "funding_closeout_receiver_claim_lots_quote",
            _normalize_funding_closeout_receiver_claim_lots(
                self.funding_closeout_receiver_claim_lots_quote,
            ),
        )
        normalized_receiver_claim_balances = _normalize_funding_closeout_receiver_claim_balances(
            self.funding_closeout_receiver_claim_balances_quote
        )
        if self.funding_closeout_receiver_claim_lots_quote:
            lot_projection = funding_closeout_receiver_claim_balances_from_lots(
                self.funding_closeout_receiver_claim_lots_quote
            )
            if normalized_receiver_claim_balances and (
                normalized_receiver_claim_balances != lot_projection
            ):
                raise ValueError("funding closeout receiver claim balance projection mismatch")
            normalized_receiver_claim_balances = lot_projection
        object.__setattr__(
            self,
            "funding_closeout_receiver_claim_balances_quote",
            normalized_receiver_claim_balances,
        )
        self._validate_isolated_state_consistency()
        self._validate_funding_closeout_sink_claimant_balances()

    def _validate_isolated_state_consistency(self) -> None:
        """Validate consensus-critical invariants on the persistent isolated-market state.

        This prevents malformed snapshots from bypassing phase gates or corrupting
        derived accounting.
        """
        validate_isolated_state_consistency(
            global_state=self.global_state,
            accounts=self.accounts,
            epoch_phase_int_to_str=_EPOCH_PHASE_INT_TO_STR,
        )

    def _validate_funding_closeout_sink_claimant_balances(self) -> None:
        total = sum(
            balance_quote for _, balance_quote in self.funding_closeout_sink_claimant_balances_quote
        )
        if total == 0:
            return
        for key in ("fee_pool_quote", "fee_income", "insurance_balance"):
            value = self.global_state.get(key)
            if not _is_non_bool_int(value):
                raise TypeError(f"global_state[{key!r}] must be an int")
            if total > int(value):
                raise ValueError(
                    "funding closeout sink claimant balances exceed aggregate sink balance"
                )

    def kernel_state_for_account(self, account: PerpAccountState) -> dict[str, Value]:
        """Project persistent market state onto the exact isolated-kernel ABI."""
        kernel_global_state = {
            key: value
            for key, value in self.global_state.items()
            if key != "mark_price_source_kind"
        }
        return {**kernel_global_state, **account.to_kernel_state()}


@dataclass(frozen=True)
class PerpClearinghouse2pMarketState:
    """Two-party clearinghouse market state (spec-driven kernel state).

    The clearinghouse kernel does not store pubkeys; we bind two pubkeys to its
    A/B account roles at the protocol layer.

    All quote amounts inside `state` are quote-e8 integers. This keeps settlement
    exact and makes the closed-system invariant checkable:
      net_deposited_e8 = collateral_e8_a + collateral_e8_b + fee_pool_e8.
    """

    quote_asset: str
    account_a_pubkey: str
    account_b_pubkey: str
    state: Dict[str, Value]
    kind: Literal["clearinghouse_2p_v1"] = PERP_MARKET_KIND_CLEARINGHOUSE_2P_V1

    def __post_init__(self) -> None:
        validate_fixed_clearinghouse_shape(
            FixedClearinghouseValidationRequest(
                kind=self.kind,
                expected_kind=PERP_MARKET_KIND_CLEARINGHOUSE_2P_V1,
                quote_asset=self.quote_asset,
                account_pubkeys=(
                    ("account_a_pubkey", self.account_a_pubkey),
                    ("account_b_pubkey", self.account_b_pubkey),
                ),
                state=self.state,
                state_keys=PERP_CLEARINGHOUSE_2P_STATE_KEYS,
                bool_keys=PERP_CLEARINGHOUSE_2P_BOOL_KEYS,
                pubkey_bytes48=_pubkey_bytes48,
            )
        )
        validate_two_party_clearinghouse_invariants(self.state)

    def role_for_pubkey(self, pubkey: str) -> Literal["a", "b"] | None:
        pb = _pubkey_bytes48_or_none(pubkey)
        if pb is None:
            return None
        if pb == _pubkey_bytes48_or_none(self.account_a_pubkey):
            return "a"
        if pb == _pubkey_bytes48_or_none(self.account_b_pubkey):
            return "b"
        return None


@dataclass(frozen=True)
class PerpClearinghouse3pTransferMarketState:
    """Three-party transfer clearinghouse market state (spec-driven kernel state).

    A/B are the active matched pair, and C is a standby account that can take over a distressed
    position if it meets initial margin.

    All quote amounts inside `state` are quote-e8 integers. This keeps settlement exact and makes
    the closed-system invariant checkable:
      net_deposited_e8 = collateral_e8_a + collateral_e8_b + collateral_e8_c + fee_pool_e8.
    """

    quote_asset: str
    account_a_pubkey: str
    account_b_pubkey: str
    account_c_pubkey: str
    state: Dict[str, Value]
    kind: Literal["clearinghouse_3p_transfer_v1"] = PERP_MARKET_KIND_CLEARINGHOUSE_3P_TRANSFER_V1

    def __post_init__(self) -> None:
        validate_fixed_clearinghouse_shape(
            FixedClearinghouseValidationRequest(
                kind=self.kind,
                expected_kind=PERP_MARKET_KIND_CLEARINGHOUSE_3P_TRANSFER_V1,
                quote_asset=self.quote_asset,
                account_pubkeys=(
                    ("account_a_pubkey", self.account_a_pubkey),
                    ("account_b_pubkey", self.account_b_pubkey),
                    ("account_c_pubkey", self.account_c_pubkey),
                ),
                state=self.state,
                state_keys=PERP_CLEARINGHOUSE_3P_TRANSFER_STATE_KEYS,
                bool_keys=PERP_CLEARINGHOUSE_3P_TRANSFER_BOOL_KEYS,
                pubkey_bytes48=_pubkey_bytes48,
            )
        )
        validate_three_party_transfer_clearinghouse_invariants(self.state)

    def role_for_pubkey(self, pubkey: str) -> Literal["a", "b", "c"] | None:
        pb = _pubkey_bytes48_or_none(pubkey)
        if pb is None:
            return None
        if pb == _pubkey_bytes48_or_none(self.account_a_pubkey):
            return "a"
        if pb == _pubkey_bytes48_or_none(self.account_b_pubkey):
            return "b"
        if pb == _pubkey_bytes48_or_none(self.account_c_pubkey):
            return "c"
        return None


@dataclass(frozen=True)
class PerpClearinghouseNpAccount:
    """One participant in an N-party clearinghouse market."""

    pubkey: str
    position_base: int = 0
    entry_price_e8: int = 0
    collateral_e8: int = 0
    funding_paid_cum_e8: int = 0
    nonce: int = 0

    def __post_init__(self) -> None:
        validate_np_account_record(account=self, pubkey_bytes48=_pubkey_bytes48)


@dataclass(frozen=True)
class PerpClearinghouseNpPendingIntent:
    """A single-signed position intent queued for the next batch match."""

    pubkey: str
    target_base: int
    nonce: int
    limit_price_e8: int = 0
    min_fill_base: int = 0
    expiry_epoch: int = 1 << 62

    def __post_init__(self) -> None:
        validate_np_pending_intent_record(intent=self, pubkey_bytes48=_pubkey_bytes48)


@dataclass(frozen=True)
class PerpClearinghouseNpMarketState:
    """Open N-party net-zero clearinghouse market state."""

    quote_asset: str
    global_state: Dict[str, int]
    accounts: tuple[PerpClearinghouseNpAccount, ...] = ()
    pending_intents: tuple[PerpClearinghouseNpPendingIntent, ...] = ()
    kind: Literal["clearinghouse_np_v1"] = PERP_MARKET_KIND_CLEARINGHOUSE_NP_V1

    def __post_init__(self) -> None:
        validate_np_market_state(
            NpMarketValidationRequest(
                kind=self.kind,
                expected_kind=PERP_MARKET_KIND_CLEARINGHOUSE_NP_V1,
                quote_asset=self.quote_asset,
                global_state=self.global_state,
                accounts=self.accounts,
                pending_intents=self.pending_intents,
                account_type=PerpClearinghouseNpAccount,
                pending_intent_type=PerpClearinghouseNpPendingIntent,
                pubkey_bytes48=_pubkey_bytes48,
            )
        )

    def by_pubkey(self) -> dict[str, PerpClearinghouseNpAccount]:
        return {a.pubkey: a for a in self.accounts}

    def role_for_pubkey(self, pubkey: str) -> str | None:
        """Return the participant's own pubkey if it is a member."""
        pb = _pubkey_bytes48_or_none(pubkey)
        if pb is None:
            return None
        for account in self.accounts:
            if pb == _pubkey_bytes48_or_none(account.pubkey):
                return account.pubkey
        return None


PerpAnyMarketState = (
    PerpMarketState
    | PerpClearinghouse2pMarketState
    | PerpClearinghouse3pTransferMarketState
    | PerpClearinghouseNpMarketState
)


@dataclass(frozen=True)
class PerpsState:
    """Top-level perps module state (can hold multiple markets)."""

    version: int
    markets: Dict[str, PerpAnyMarketState]

    def __post_init__(self) -> None:
        if not isinstance(self.version, int) or isinstance(self.version, bool) or self.version <= 0:
            raise TypeError("version must be a positive int")
        if self.version not in (PERPS_STATE_VERSION_V4, PERPS_STATE_VERSION_V5):
            raise ValueError(f"unsupported perps state version: {self.version}")
        if not isinstance(self.markets, dict):
            raise TypeError("markets must be a dict")
        if self.version == PERPS_STATE_VERSION_V4:
            for market_id, market in self.markets.items():
                if not isinstance(market_id, str):
                    raise TypeError("markets keys must be strings")
                if not isinstance(market, PerpMarketState):
                    raise TypeError("perps v4 supports isolated markets only")

    def get_market(self, market_id: str) -> PerpAnyMarketState | None:
        return self.markets.get(market_id)
