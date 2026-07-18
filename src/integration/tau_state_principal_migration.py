"""Atomic Tau principal migration for persisted value-moving state.

Tau accepts BLS public keys with or without an ``0x`` prefix. ZenoDEX uses the
prefixed spelling inside committed state. This adapter owns that representation
change across every principal-keyed table that shares the DEX snapshot. It
rejects alias collisions before returning any migrated state.
"""

from __future__ import annotations

from dataclasses import replace
from typing import Iterable, TypeVar

from ..core.dex import DexState
from ..core.perps import (
    PerpClearinghouse2pMarketState,
    PerpClearinghouse3pTransferMarketState,
    PerpClearinghouseNpMarketState,
    PerpMarketState,
    PerpsState,
)
from ..state.balances import BalanceTable
from ..state.canonical import canonical_hex_fixed_allow_0x
from ..state.lp import LPDurationRiskMetadata, LPTable
from ..state.nonces import NonceTable

_T = TypeVar("_T")


def _canonical_principal(value: object, *, name: str) -> str:
    return canonical_hex_fixed_allow_0x(value, nbytes=48, name=name)


def _record_unique_spelling(
    seen: dict[tuple[str, str], str],
    *,
    canonical_pubkey: str,
    secondary_key: str,
    source_pubkey: str,
    table_name: str,
) -> None:
    logical_key = (canonical_pubkey, secondary_key)
    prior = seen.get(logical_key)
    if prior is not None and prior != source_pubkey:
        raise ValueError(
            f"{table_name} has ambiguous principal spellings for "
            f"{canonical_pubkey}:{secondary_key}: {prior!r}, {source_pubkey!r}"
        )
    seen[logical_key] = source_pubkey


def _canonical_balances(source: BalanceTable) -> tuple[BalanceTable, bool]:
    migrated = BalanceTable()
    changed = False
    spellings: dict[tuple[str, str], str] = {}
    for (pubkey, asset), amount in sorted(source.get_all_balances().items()):
        canonical = _canonical_principal(pubkey, name="balance pubkey")
        changed = changed or canonical != pubkey
        _record_unique_spelling(
            spellings,
            canonical_pubkey=canonical,
            secondary_key=asset,
            source_pubkey=pubkey,
            table_name="balances",
        )
        migrated.set(canonical, asset, amount)
    return migrated, changed


def _canonical_lp_balances(source: LPTable) -> tuple[LPTable, bool]:
    migrated = LPTable()
    changed = False
    balance_spellings: dict[tuple[str, str], str] = {}
    for (pubkey, pool_id), amount in sorted(source.get_all_balances().items()):
        canonical = _canonical_principal(pubkey, name="LP balance pubkey")
        changed = changed or canonical != pubkey
        _record_unique_spelling(
            balance_spellings,
            canonical_pubkey=canonical,
            secondary_key=pool_id,
            source_pubkey=pubkey,
            table_name="LP balances",
        )
        migrated.set(canonical, pool_id, amount)

    metadata_by_key: dict[tuple[str, str], LPDurationRiskMetadata] = {}
    metadata_spellings: dict[tuple[str, str], str] = {}
    for (pubkey, pool_id), metadata in sorted(source.get_all_duration_risk_metadata().items()):
        canonical = _canonical_principal(pubkey, name="LP metadata pubkey")
        changed = changed or canonical != pubkey
        _record_unique_spelling(
            metadata_spellings,
            canonical_pubkey=canonical,
            secondary_key=pool_id,
            source_pubkey=pubkey,
            table_name="LP duration metadata",
        )
        metadata_by_key[(canonical, pool_id)] = metadata

    for (canonical, pool_id), metadata in sorted(metadata_by_key.items()):
        if metadata.last_mint_timestamp is not None:
            migrated.set_last_mint_timestamp(
                canonical,
                pool_id,
                metadata.last_mint_timestamp,
            )
        if metadata.last_remove_timestamp is not None:
            migrated.set_last_remove_timestamp(
                canonical,
                pool_id,
                metadata.last_remove_timestamp,
            )
        if metadata.churn_tier > 0:
            migrated.set_churn_tier(canonical, pool_id, metadata.churn_tier)
        if metadata.last_churn_update_timestamp is not None:
            migrated.set_last_churn_update_timestamp(
                canonical,
                pool_id,
                metadata.last_churn_update_timestamp,
            )
    return migrated, changed


def _canonical_nonces(source: NonceTable) -> tuple[NonceTable, bool]:
    migrated = NonceTable()
    changed = False
    spellings: dict[str, str] = {}
    for pubkey, last_nonce in sorted(source.get_all().items()):
        canonical = _canonical_principal(pubkey, name="nonce pubkey")
        changed = changed or canonical != pubkey
        prior = spellings.get(canonical)
        if prior is not None and prior != pubkey:
            raise ValueError(
                f"nonces has ambiguous principal spellings for {canonical}: {prior!r}, {pubkey!r}"
            )
        spellings[canonical] = pubkey
        migrated.set_last(canonical, last_nonce)
    return migrated, changed


def _canonical_rows(
    rows: Iterable[tuple[str, _T]],
    *,
    name: str,
) -> tuple[tuple[tuple[str, _T], ...], bool]:
    migrated: dict[str, tuple[str, _T]] = {}
    changed = False
    for source_pubkey, value in rows:
        canonical = _canonical_principal(source_pubkey, name=name)
        changed = changed or canonical != source_pubkey
        prior = migrated.get(canonical)
        if prior is not None and prior[0] != source_pubkey:
            raise ValueError(
                f"{name} has ambiguous principal spellings for {canonical}: "
                f"{prior[0]!r}, {source_pubkey!r}"
            )
        migrated[canonical] = (source_pubkey, value)
    return tuple((key, row[1]) for key, row in sorted(migrated.items())), changed


def _canonical_isolated_market(market: PerpMarketState) -> tuple[PerpMarketState, bool]:
    account_rows, accounts_changed = _canonical_rows(
        market.accounts.items(),
        name="isolated perps account",
    )
    receiver_rows, receiver_changed = _canonical_rows(
        market.funding_closeout_receiver_claim_balances_quote,
        name="funding closeout receiver account",
    )

    lot_spellings: dict[tuple[str, str], str] = {}
    lots: list[tuple[str, str, int, int]] = []
    lots_changed = False
    for (
        account_pubkey,
        lot_id,
        balance_quote,
        expires_at_epoch,
    ) in market.funding_closeout_receiver_claim_lots_quote:
        canonical = _canonical_principal(
            account_pubkey,
            name="funding closeout receiver lot account",
        )
        lots_changed = lots_changed or canonical != account_pubkey
        _record_unique_spelling(
            lot_spellings,
            canonical_pubkey=canonical,
            secondary_key=lot_id,
            source_pubkey=account_pubkey,
            table_name="funding closeout receiver lots",
        )
        lots.append((canonical, lot_id, balance_quote, expires_at_epoch))

    changed = accounts_changed or receiver_changed or lots_changed
    if not changed:
        return market, False
    account_bound_evidence_present = any(
        (
            market.pending_funding_closeout_root_hashes,
            market.pending_funding_closeout_source_availability_hashes,
            market.pending_funding_closeout_carried_liability_hashes,
            market.funding_closeout_policy_ledger_hashes,
            market.funding_closeout_receiver_claim_balances_quote,
            market.funding_closeout_receiver_claim_lots_quote,
        )
    )
    if account_bound_evidence_present:
        raise ValueError(
            "cannot migrate noncanonical isolated perps identities while "
            "account-bound funding closeout evidence is outstanding"
        )
    return (
        replace(
            market,
            global_state=dict(market.global_state),
            accounts=dict(account_rows),
            funding_closeout_receiver_claim_balances_quote=tuple(receiver_rows),
            funding_closeout_receiver_claim_lots_quote=tuple(sorted(lots)),
        ),
        True,
    )


def _canonical_fixed_market(
    market: PerpClearinghouse2pMarketState | PerpClearinghouse3pTransferMarketState,
) -> tuple[
    PerpClearinghouse2pMarketState | PerpClearinghouse3pTransferMarketState,
    bool,
]:
    account_a = _canonical_principal(
        market.account_a_pubkey,
        name="clearinghouse account_a_pubkey",
    )
    account_b = _canonical_principal(
        market.account_b_pubkey,
        name="clearinghouse account_b_pubkey",
    )
    updates = {
        "account_a_pubkey": account_a,
        "account_b_pubkey": account_b,
    }
    changed = account_a != market.account_a_pubkey or account_b != market.account_b_pubkey
    if isinstance(market, PerpClearinghouse3pTransferMarketState):
        account_c = _canonical_principal(
            market.account_c_pubkey,
            name="clearinghouse account_c_pubkey",
        )
        updates["account_c_pubkey"] = account_c
        changed = changed or account_c != market.account_c_pubkey
    if not changed:
        return market, False
    return replace(market, state=dict(market.state), **updates), True


def _canonical_np_market(
    market: PerpClearinghouseNpMarketState,
) -> tuple[PerpClearinghouseNpMarketState, bool]:
    account_rows, accounts_changed = _canonical_rows(
        ((account.pubkey, account) for account in market.accounts),
        name="N-party perps account",
    )
    pending_rows, pending_changed = _canonical_rows(
        ((intent.pubkey, intent) for intent in market.pending_intents),
        name="N-party pending intent",
    )
    if not (accounts_changed or pending_changed):
        return market, False
    accounts = tuple(replace(account, pubkey=canonical) for canonical, account in account_rows)
    pending_intents = tuple(replace(intent, pubkey=canonical) for canonical, intent in pending_rows)
    return (
        replace(
            market,
            global_state=dict(market.global_state),
            accounts=accounts,
            pending_intents=pending_intents,
        ),
        True,
    )


def _canonical_perps(source: PerpsState | None) -> tuple[PerpsState | None, bool]:
    if source is None:
        return None, False
    markets = {}
    changed = False
    for market_id, market in sorted(source.markets.items()):
        if isinstance(market, PerpMarketState):
            migrated, market_changed = _canonical_isolated_market(market)
        elif isinstance(
            market,
            (PerpClearinghouse2pMarketState, PerpClearinghouse3pTransferMarketState),
        ):
            migrated, market_changed = _canonical_fixed_market(market)
        elif isinstance(market, PerpClearinghouseNpMarketState):
            migrated, market_changed = _canonical_np_market(market)
        else:
            raise TypeError(f"unsupported perps market state: {type(market).__name__}")
        markets[market_id] = migrated
        changed = changed or market_changed
    if not changed:
        return source, False
    return replace(source, markets=markets), True


def canonicalize_legacy_tau_state_principals(state: DexState) -> DexState:
    """Return an owned canonical Tau state or reject an alias collision."""

    balances, balances_changed = _canonical_balances(state.balances)
    lp_balances, lp_changed = _canonical_lp_balances(state.lp_balances)
    nonces, nonces_changed = _canonical_nonces(state.nonces)
    perps, perps_changed = _canonical_perps(state.perps)
    if not (balances_changed or lp_changed or nonces_changed or perps_changed):
        return state
    return replace(
        state,
        balances=balances,
        lp_balances=lp_balances,
        nonces=nonces,
        perps=perps,
    )
