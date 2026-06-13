"""Characterization + teeth tests for the live zUSD monetary bridge.

This file pins the *exact* observable behavior of
``src.integration.zusd_monetary_bridge.apply_zusd_monetary_ops`` and, through it,
the per-operation dispatch performed by ``_apply_one``.

Why drive the *public* boundary instead of ``_apply_one`` directly:
``_apply_one`` mutates the ``balances`` table in place and may mutate it *before*
its final ``_raise_if_bad_state`` check (e.g. ``deposit_collateral`` subtracts
native balance and only then validates). The fail-closed / **no-op-on-reject**
contract is therefore a *transaction-boundary* property: ``apply_zusd_monetary_ops``
operates on private *copies* of the balance/nonce tables and discards them on any
exception. So every reject assertion below checks that the **input** ``DexState``
(its balances and nonces) is byte-identical after a rejected call, that
``result.ok is False`` and ``result.state is None``, and that the error string is
exactly preserved.

These are golden/oracle tests: they must stay IDENTICALLY GREEN across the
``_apply_one`` complexity refactor. If a test changes, fix the refactor, never the
test.
"""

from __future__ import annotations

import copy

import pytest

from src.core.dex import DexState
from src.core.zusd import E8
from src.state import BalanceTable, LPTable
from src.state.balances import NATIVE_ASSET
from src.integration.tau_net_client import bls_pubkey_hex_from_privkey
from src.integration.zusd_monetary_bridge import (
    ZUSDMonetaryConfig,
    ZUSDMonetaryTxResult,
    apply_zusd_monetary_ops,
    stability_pool_pubkey,
    zusd_monetary_sender_nonce_key,
    _raw_pubkey_key,
)


# ---------------------------------------------------------------------------
# Fixtures / harness
# ---------------------------------------------------------------------------

CHAIN = "tau-local"
ALICE = "0x" + bls_pubkey_hex_from_privkey(82)
BOB = "0x" + bls_pubkey_hex_from_privkey(83)
ORACLE = "0x" + bls_pubkey_hex_from_privkey(81)

# native balances resolve to the *raw* (no-0x) sender key; zUSD balances resolve
# to the canonical (0x-prefixed) sender key. Pin both forms explicitly.
ALICE_RAW, _ = _raw_pubkey_key(ALICE)


def _cfg(**overrides) -> ZUSDMonetaryConfig:
    base = dict(chain_id=CHAIN, oracle_pubkey=ORACLE)
    base.update(overrides)
    return ZUSDMonetaryConfig(**base)


def _asset(cfg: ZUSDMonetaryConfig) -> str:
    return cfg.zusd_asset


def _sp(cfg: ZUSDMonetaryConfig) -> str:
    return stability_pool_pubkey(chain_id=cfg.chain_id)


def _funded_state(native_e8: int = 1000 * E8) -> DexState:
    bt = BalanceTable()
    bt.set(ALICE_RAW, NATIVE_ASSET, native_e8)
    return DexState(balances=bt, pools={}, lp_balances=LPTable())


def _op(action: str, nonce: int, **kwargs) -> dict:
    op = {"module": "ZUSDFinance", "version": "0.1", "action": action, "nonce": nonce}
    op.update(kwargs)
    return op


def _balances_snapshot(state: DexState) -> dict:
    return dict(state.balances.get_all_balances())


def _nonces_snapshot(state: DexState) -> dict:
    return dict(state.nonces.get_all())


def _apply(
    cfg: ZUSDMonetaryConfig,
    state: DexState,
    zusd_state,
    ops,
    *,
    sender: str,
    ts: int = 10,
) -> ZUSDMonetaryTxResult:
    return apply_zusd_monetary_ops(
        config=cfg,
        state=state,
        zusd_state=zusd_state,
        operations=ops,
        tx_sender_pubkey=sender,
        block_timestamp=ts,
    )


def _ok(result: ZUSDMonetaryTxResult) -> ZUSDMonetaryTxResult:
    assert result.ok, result.error
    assert result.state is not None
    assert result.zusd_state is not None
    return result


def _last_effect(result: ZUSDMonetaryTxResult) -> dict:
    assert result.effects
    return result.effects[-1]["effects"]


class _Ctx:
    """A live, advancing bridge context that replays ops to reach valid states.

    Fixtures must be built by replaying ops through the public API (not hand-built
    state) because SP ops are gated by ``_assert_sp_escrow_matches`` and
    ``_state_invariant_error`` (escrow == sp_debt units, sum(deposits)==sp_debt_e8).
    """

    def __init__(self, cfg: ZUSDMonetaryConfig, state: DexState):
        self.cfg = cfg
        self.state = state
        self.zusd = None

    def run(self, ops, *, sender: str, ts: int = 10) -> ZUSDMonetaryTxResult:
        r = _apply(self.cfg, self.state, self.zusd, ops, sender=sender, ts=ts)
        return r

    def advance(self, ops, *, sender: str, ts: int = 10) -> ZUSDMonetaryTxResult:
        r = _ok(self.run(ops, sender=sender, ts=ts))
        self.state = r.state
        self.zusd = r.zusd_state
        return r


def _bootstrapped() -> _Ctx:
    cfg = _cfg()
    ctx = _Ctx(cfg, _funded_state())
    ctx.advance([_op("bootstrap_oracle", 1, price_e8=100 * E8)], sender=ORACLE)
    return ctx


def _vault_open() -> _Ctx:
    """Oracle bootstrapped + Alice has collateral and 100 zUSD minted."""
    ctx = _bootstrapped()
    ctx.advance(
        [
            _op("deposit_collateral", 1, amount_e8=20 * E8),
            _op("mint_zusd", 2, amount_e8=100 * E8),
        ],
        sender=ALICE,
    )
    return ctx


def _sp_funded() -> _Ctx:
    """Vault open + Alice's 100 zUSD deposited into the stability pool."""
    ctx = _vault_open()
    ctx.advance([_op("deposit_sp", 3, amount_e8=100 * E8)], sender=ALICE)
    return ctx


def _liquidated() -> _Ctx:
    """SP funded, oracle pending dropped below MCR, vault liquidated.

    Leaves a non-zero SP collateral claim for Alice (claim_sp_collateral target).
    """
    ctx = _sp_funded()
    ctx.advance([_op("oracle_report", 2, price_e8=1 * E8)], sender=ORACLE)
    ctx.advance([_op("liquidate", 4)], sender=ALICE)
    return ctx


# ---------------------------------------------------------------------------
# Reject helper: asserts fail-closed + no-op-on-reject + exact error string.
# ---------------------------------------------------------------------------

def _assert_reject_noop(
    ctx: _Ctx,
    ops,
    *,
    sender: str,
    error: str,
    ts: int = 10,
) -> None:
    bal_before = _balances_snapshot(ctx.state)
    nonces_before = _nonces_snapshot(ctx.state)
    zusd_before = copy.deepcopy(ctx.zusd)

    result = ctx.run(ops, sender=sender, ts=ts)

    assert result.ok is False, f"expected reject, got ok with effects={result.effects}"
    assert result.state is None
    assert result.zusd_state is None
    assert result.error == error, f"\n  expected: {error!r}\n  actual:   {result.error!r}"

    # no-op-on-reject: input DexState (balances + nonces) byte-identical.
    assert _balances_snapshot(ctx.state) == bal_before
    assert _nonces_snapshot(ctx.state) == nonces_before
    # monetary state object the caller passed in is unchanged (and unreturned).
    assert copy.deepcopy(ctx.zusd) == zusd_before


# ===========================================================================
# SUCCESS CASES — one per operation (assert resulting state + effect dict)
# ===========================================================================

def test_success_bootstrap_oracle():
    cfg = _cfg()
    ctx = _Ctx(cfg, _funded_state())
    r = ctx.advance([_op("bootstrap_oracle", 1, price_e8=100 * E8)], sender=ORACLE)
    assert _last_effect(r) == {"event": "oracle_bootstrapped", "price_e8": 100 * E8}
    assert ctx.zusd.core.oracle_seen is True
    assert ctx.zusd.core.price_e8 == 100 * E8


def test_success_advance_epoch():
    ctx = _bootstrapped()
    r = ctx.advance([_op("advance_epoch", 1, delta=5)], sender=ALICE)
    assert _last_effect(r) == {"event": "epoch_advanced", "delta": 5}
    assert ctx.zusd.core.now_epoch == 5


def test_success_oracle_report():
    ctx = _bootstrapped()
    r = ctx.advance([_op("oracle_report", 2, price_e8=50 * E8)], sender=ORACLE)
    assert _last_effect(r) == {"event": "oracle_reported", "price_pending_e8": 50 * E8}
    assert ctx.zusd.core.price_pending_e8 == 50 * E8


def test_success_oracle_commit():
    ctx = _bootstrapped()
    # advance an epoch so the committed update epoch moves, then commit.
    ctx.advance([_op("advance_epoch", 1, delta=3)], sender=ALICE)
    r = ctx.advance([_op("oracle_commit", 2)], sender=ORACLE)
    assert _last_effect(r) == {"event": "oracle_committed", "price_e8": 100 * E8}
    assert ctx.zusd.core.oracle_last_update_epoch == 3


def test_success_deposit_collateral_initializes_owner():
    ctx = _bootstrapped()
    r = ctx.advance([_op("deposit_collateral", 1, amount_e8=20 * E8)], sender=ALICE)
    eff = _last_effect(r)
    assert eff["event"] == "collateral_deposited"
    assert eff["amount_e8"] == 20 * E8
    assert eff["native_balance_delta_e8"] == -20 * E8
    # owner initialized to sender on first deposit of a fresh vault.
    assert ctx.zusd.vault_owner_pubkey == ALICE
    assert ctx.zusd.core.collateral_e8 == 20 * E8
    # native debited under the raw sender key.
    assert ctx.state.balances.get(ALICE_RAW, NATIVE_ASSET) == 1000 * E8 - 20 * E8


def test_success_mint_zusd():
    ctx = _vault_open()  # already minted 100 in setup
    eff_setup = None  # mint happened in setup; re-mint a second tranche here
    r = ctx.advance([_op("mint_zusd", 3, amount_e8=50 * E8)], sender=ALICE)
    eff = _last_effect(r)
    assert eff["event"] == "zusd_minted"
    assert eff["principal_e8"] == 50 * E8
    assert eff["zusd_balance_delta"] == 50  # whole units
    # zUSD credited under canonical (0x) sender key; 100 + 50 = 150 units.
    assert ctx.state.balances.get(ALICE, _asset(ctx.cfg)) == 150


def test_success_repay_zusd():
    ctx = _vault_open()
    r = ctx.advance([_op("repay_zusd", 3, amount_e8=100 * E8)], sender=ALICE)
    eff = _last_effect(r)
    assert eff["event"] == "zusd_repaid"
    assert eff["amount_e8"] == 100 * E8
    assert eff["zusd_balance_delta"] == -100
    assert ctx.state.balances.get(ALICE, _asset(ctx.cfg)) == 0


def test_success_withdraw_collateral():
    ctx = _vault_open()
    native_before = ctx.state.balances.get(ALICE_RAW, NATIVE_ASSET)
    r = ctx.advance([_op("withdraw_collateral", 3, amount_e8=1 * E8)], sender=ALICE)
    eff = _last_effect(r)
    assert eff["event"] == "collateral_withdrawn"
    assert eff["amount_e8"] == 1 * E8
    assert eff["native_balance_delta_e8"] == 1 * E8
    assert ctx.state.balances.get(ALICE_RAW, NATIVE_ASSET) == native_before + 1 * E8


def test_success_deposit_sp():
    ctx = _vault_open()
    r = ctx.advance([_op("deposit_sp", 3, amount_e8=100 * E8)], sender=ALICE)
    eff = _last_effect(r)
    assert eff["event"] == "sp_deposited"
    assert eff["zusd_balance_delta"] == -100
    assert eff["sp_escrow_delta"] == 100
    asset = _asset(ctx.cfg)
    assert ctx.state.balances.get(ALICE, asset) == 0
    assert ctx.state.balances.get(_sp(ctx.cfg), asset) == 100
    assert dict(ctx.zusd.sp_deposits_e8) == {ALICE: 100 * E8}


def test_success_withdraw_sp():
    ctx = _sp_funded()
    r = ctx.advance([_op("withdraw_sp", 4, amount_e8=40 * E8)], sender=ALICE)
    eff = _last_effect(r)
    assert eff["event"] == "sp_withdrawn"
    assert eff["zusd_balance_delta"] == 40
    assert eff["sp_escrow_delta"] == -40
    asset = _asset(ctx.cfg)
    assert ctx.state.balances.get(ALICE, asset) == 40
    assert ctx.state.balances.get(_sp(ctx.cfg), asset) == 60
    assert dict(ctx.zusd.sp_deposits_e8) == {ALICE: 60 * E8}


def test_success_redeem_zusd():
    # need debt remaining + zUSD in wallet; mint 200, redeem 50.
    cfg = _cfg()
    ctx = _Ctx(cfg, _funded_state())
    ctx.advance([_op("bootstrap_oracle", 1, price_e8=100 * E8)], sender=ORACLE)
    ctx.advance(
        [
            _op("deposit_collateral", 1, amount_e8=20 * E8),
            _op("mint_zusd", 2, amount_e8=200 * E8),
        ],
        sender=ALICE,
    )
    native_before = ctx.state.balances.get(ALICE_RAW, NATIVE_ASSET)
    r = ctx.advance([_op("redeem_zusd", 3, amount_e8=50 * E8)], sender=ALICE)
    eff = _last_effect(r)
    assert eff["event"] == "zusd_redeemed"
    assert eff["redeemed_zusd_e8"] == 50 * E8
    assert eff["zusd_balance_delta"] == -50
    collateral_out = eff["native_balance_delta_e8"]
    assert collateral_out == eff["redeemed_collateral_out_e8"]
    assert ctx.state.balances.get(ALICE, _asset(ctx.cfg)) == 150
    assert ctx.state.balances.get(ALICE_RAW, NATIVE_ASSET) == native_before + collateral_out


def test_success_liquidate():
    ctx = _sp_funded()
    ctx.advance([_op("oracle_report", 2, price_e8=1 * E8)], sender=ORACLE)
    asset = _asset(ctx.cfg)
    escrow_before = ctx.state.balances.get(_sp(ctx.cfg), asset)
    r = ctx.advance([_op("liquidate", 4)], sender=ALICE)
    eff = _last_effect(r)
    assert eff["event"] == "liquidated"
    assert eff["liquidated_debt_e8"] == 100 * E8
    assert eff["sp_escrow_delta"] == -100
    # SP escrow burned by the debt units.
    assert ctx.state.balances.get(_sp(ctx.cfg), asset) == escrow_before - 100
    # collateral claim recorded for the single SP depositor.
    assert dict(ctx.zusd.sp_collateral_claims_e8) == {ALICE: eff["sp_collateral_gain_e8"]}
    assert ctx.zusd.core.debt_e8 == 0
    assert ctx.zusd.core.collateral_e8 == 0


def test_success_claim_sp_collateral():
    ctx = _liquidated()
    claim_before = int(ctx.zusd.sp_collateral_claims_e8[ALICE])
    native_before = ctx.state.balances.get(ALICE_RAW, NATIVE_ASSET)
    r = ctx.advance([_op("claim_sp_collateral", 5, amount_e8=1 * E8)], sender=ALICE)
    eff = _last_effect(r)
    assert eff == {
        "event": "sp_collateral_claimed",
        "amount_e8": 1 * E8,
        "native_balance_delta_e8": 1 * E8,
    }
    assert ctx.state.balances.get(ALICE_RAW, NATIVE_ASSET) == native_before + 1 * E8
    assert int(ctx.zusd.sp_collateral_claims_e8.get(ALICE, 0)) == claim_before - 1 * E8
    assert ctx.zusd.core.sp_coll_e8 == claim_before - 1 * E8


# ===========================================================================
# REJECT CASES — one per operation (exact reject code + no-op-on-reject)
# ===========================================================================

def test_reject_bootstrap_oracle_wrong_sender():
    # bridge guard: oracle action requires oracle sender. raised at index 0.
    ctx = _Ctx(_cfg(), _funded_state())
    _assert_reject_noop(
        ctx,
        [_op("bootstrap_oracle", 1, price_e8=100 * E8)],
        sender=ALICE,
        error="zusd op[0] zUSD oracle action requires oracle sender",
    )


def test_reject_advance_epoch_bad_delta():
    ctx = _bootstrapped()
    _assert_reject_noop(
        ctx,
        [_op("advance_epoch", 1, delta=0)],
        sender=ALICE,
        error="zusd op[0] advance_epoch.delta must be >= 1",
    )


def test_reject_oracle_report_increasing_price():
    # core passthrough reject: oracle_report requires non-increasing pending price.
    ctx = _bootstrapped()
    _assert_reject_noop(
        ctx,
        [_op("oracle_report", 2, price_e8=200 * E8)],
        sender=ORACLE,
        error="zusd op[0] oracle_report requires non-increasing pending price",
    )


def test_reject_oracle_commit_below_mcr():
    # report a crushing pending price, then commit blocked at pending price.
    # ORACLE used nonce 1 for bootstrap, so the next oracle op is nonce 2.
    ctx = _vault_open()
    ctx.advance([_op("oracle_report", 2, price_e8=1 * E8)], sender=ORACLE)
    _assert_reject_noop(
        ctx,
        [_op("oracle_commit", 3)],
        sender=ORACLE,
        error="zusd op[0] oracle_commit blocked: vault below MCR at pending price",
    )


def test_reject_deposit_collateral_insufficient_native():
    ctx = _bootstrapped()
    _assert_reject_noop(
        ctx,
        [_op("deposit_collateral", 1, amount_e8=5000 * E8)],
        sender=ALICE,
        error="zusd op[0] insufficient native collateral balance",
    )


def test_reject_mint_zusd_uninitialized_vault():
    # mint on a vault with no owner yet -> bridge guard "vault owner not initialized".
    ctx = _bootstrapped()
    _assert_reject_noop(
        ctx,
        [_op("mint_zusd", 1, amount_e8=100 * E8)],
        sender=ALICE,
        error="zusd op[0] vault owner not initialized",
    )


def test_reject_withdraw_collateral_exceeds():
    ctx = _vault_open()
    _assert_reject_noop(
        ctx,
        [_op("withdraw_collateral", 3, amount_e8=9999 * E8)],
        sender=ALICE,
        error="zusd op[0] insufficient collateral",
    )


def test_reject_repay_zusd_insufficient_balance():
    # vault has 100 debt but wallet only holds 100 units; repay 200 -> wallet check.
    # Mint 100 (setup) then move all zUSD to SP so wallet balance is 0, then repay.
    ctx = _vault_open()
    _assert_reject_noop(
        ctx,
        [_op("repay_zusd", 3, amount_e8=200 * E8)],
        sender=ALICE,
        error="zusd op[0] insufficient zUSD balance",
    )


def test_reject_deposit_sp_insufficient_balance():
    # TEETH (validate-before-mutate): _apply_deposit_sp checks the wallet balance
    # BEFORE it subtracts from the depositor and credits the SP escrow. The
    # catching mechanism is the EXACT error-string assert below, not the no-op
    # check: the caller works on a discarded copy, so the input state is
    # byte-identical on reject regardless of what the handler did before raising.
    # But moving the `subtract` ahead of this guard underflows the balance table
    # and raises BalanceTable's "Insufficient balance: ..." instead of this
    # bridge guard -> the asserted string flips and the test fails.
    ctx = _vault_open()
    _assert_reject_noop(
        ctx,
        [_op("deposit_sp", 3, amount_e8=500 * E8)],
        sender=ALICE,
        error="zusd op[0] insufficient zUSD balance",
    )


def test_reject_withdraw_sp_exceeds_deposit():
    ctx = _sp_funded()
    _assert_reject_noop(
        ctx,
        [_op("withdraw_sp", 4, amount_e8=500 * E8)],
        sender=ALICE,
        error="zusd op[0] withdraw_sp exceeds account deposit",
    )


def test_reject_redeem_zusd_insufficient_balance():
    # vault open with 100 zUSD; redeem 500 -> wallet balance check fails first.
    ctx = _vault_open()
    _assert_reject_noop(
        ctx,
        [_op("redeem_zusd", 3, amount_e8=500 * E8)],
        sender=ALICE,
        error="zusd op[0] insufficient zUSD balance",
    )


def test_reject_liquidate_vault_not_under_mcr():
    # SP funded, price healthy -> vault not under MCR at pending price (core reject).
    ctx = _sp_funded()
    _assert_reject_noop(
        ctx,
        [_op("liquidate", 4)],
        sender=ALICE,
        error="zusd op[0] vault not under MCR at pending price",
    )


def test_reject_claim_sp_collateral_exceeds_gain():
    ctx = _liquidated()
    _assert_reject_noop(
        ctx,
        [_op("claim_sp_collateral", 5, amount_e8=9999 * E8)],
        sender=ALICE,
        error="zusd op[0] claim exceeds account collateral gain",
    )


def test_reject_unknown_action():
    ctx = _bootstrapped()
    # unknown action is rejected by _require_action before _apply_one dispatch.
    _assert_reject_noop(
        ctx,
        [_op("teleport_funds", 1, amount_e8=1)],
        sender=ALICE,
        error="zusd op[0] action unsupported: 'teleport_funds'",
    )


# ===========================================================================
# PRECEDENCE CASES — two checks could fire; pin which wins.
# ===========================================================================

def test_precedence_owner_mismatch_before_amount_validation():
    # For deposit_collateral, the shared owner-resolution block (owner_pubkey !=
    # sender) must fire BEFORE amount_e8 validation. amount_e8 is invalid (0) AND
    # owner_pubkey is wrong; owner mismatch must win.
    ctx = _bootstrapped()
    _assert_reject_noop(
        ctx,
        [_op("deposit_collateral", 1, owner_pubkey=BOB, amount_e8=0)],
        sender=ALICE,
        error="zusd op[0] owner_pubkey mismatch",
    )


def test_precedence_vault_owner_mismatch_for_existing_vault():
    # Vault owned by ALICE; BOB tries to mint. owner-block raises "vault owner
    # mismatch" (distinct from the uninitialized case).
    ctx = _vault_open()
    _assert_reject_noop(
        ctx,
        [_op("mint_zusd", 1, amount_e8=50 * E8)],
        sender=BOB,
        error="zusd op[0] vault owner mismatch",
    )


def test_precedence_nonce_before_deadline():
    # A bad nonce AND an expired deadline are both present. The nonce check runs
    # first in apply_zusd_monetary_ops, so the nonce error must win.
    ctx = _bootstrapped()
    bal_before = _balances_snapshot(ctx.state)
    nonces_before = _nonces_snapshot(ctx.state)
    result = ctx.run(
        [_op("advance_epoch", 99, delta=1, deadline=1)],
        sender=ALICE,
        ts=10_000,
    )
    assert result.ok is False
    assert result.state is None
    assert result.error == "zusd op[0] nonce invalid (expected 1, got 99)"
    assert _balances_snapshot(ctx.state) == bal_before
    assert _nonces_snapshot(ctx.state) == nonces_before


def test_precedence_deadline_before_unknown_fields():
    # Expired deadline AND an unknown field both present, nonce valid. Deadline
    # check runs before the unknown-field check.
    ctx = _bootstrapped()
    _assert_reject_noop(
        ctx,
        [_op("advance_epoch", 1, delta=1, deadline=1, bogus_field=7)],
        sender=ALICE,
        error="zusd op[0].deadline expired",
        ts=10_000,
    )


def test_precedence_unknown_field_before_apply():
    # Unknown field for the action is rejected before _apply_one dispatch even
    # though the op is otherwise valid.
    ctx = _bootstrapped()
    _assert_reject_noop(
        ctx,
        [_op("advance_epoch", 1, delta=1, surprise=1)],
        sender=ALICE,
        error="zusd op[0] unknown fields: ['surprise']",
    )


# ===========================================================================
# MULTI-OP ATOMICITY — a reject mid-stream rolls back earlier ops in the tx.
# ===========================================================================

def test_multi_op_reject_midstream_is_full_noop():
    # TEETH (transaction-boundary no-op-on-reject): op[0] deposit + op[1] mint
    # succeed against the working *copy*, op[2] rejects. Because _apply_one
    # mutates the balances table in place, the committed deposit/mint deltas live
    # in that copy at the moment op[2] raises. The no-op guarantee holds only
    # because apply_zusd_monetary_ops discards the copy on exception. If a
    # refactor moved `next_state = replace(state, balances=...)` inside the loop,
    # or applied effects to the *input* tables instead of copies, op[0]/op[1]
    # would leak into committed state and this assertion would fail.
    ctx = _bootstrapped()
    bal_before = _balances_snapshot(ctx.state)
    nonces_before = _nonces_snapshot(ctx.state)
    result = ctx.run(
        [
            _op("deposit_collateral", 1, amount_e8=20 * E8),
            _op("mint_zusd", 2, amount_e8=100 * E8),
            _op("withdraw_collateral", 3, amount_e8=9999 * E8),  # rejects
        ],
        sender=ALICE,
    )
    assert result.ok is False
    assert result.state is None
    assert result.error == "zusd op[2] insufficient collateral"
    # earlier (committed-to-copy) deposit/mint are discarded: input untouched.
    assert _balances_snapshot(ctx.state) == bal_before
    assert _nonces_snapshot(ctx.state) == nonces_before


# ===========================================================================
# TEETH — fail if the refactor drops a dispatch entry, breaks owner threading,
# or changes a reject code. Each test is commented with the mutation it catches.
#
# NOTE: The whole REJECT CASES block above is also teeth for "a reject code
# changes": every reject test asserts the EXACT error string (e.g. a typo in
# "insufficient zUSD balance", or routing an op to the wrong handler so a
# different guard fires first, flips the string and fails the test).
# ===========================================================================

def test_teeth_dispatch_table_is_complete_and_exact():
    # TEETH (dropped/typo'd dispatch entry — the failure mode unique to the
    # if/elif -> dict refactor): the dict-dispatch _APPLY_DISPATCH must map
    # EXACTLY the 13 supported actions. If a refactor drops an entry, renames a
    # key, or adds a stray one, this fails. The 13 here mirror _require_action's
    # allowlist; any action that reaches _apply_one without a dispatch entry is
    # rejected with "unknown action" (covered by test_teeth_unmapped_action_*).
    from src.integration.zusd_monetary_bridge import _APPLY_DISPATCH

    assert set(_APPLY_DISPATCH) == {
        "bootstrap_oracle",
        "oracle_report",
        "oracle_commit",
        "advance_epoch",
        "deposit_collateral",
        "withdraw_collateral",
        "mint_zusd",
        "repay_zusd",
        "deposit_sp",
        "withdraw_sp",
        "redeem_zusd",
        "liquidate",
        "claim_sp_collateral",
    }
    # the three oracle actions must all route to the same handler (they shared one
    # branch in the original); a refactor splitting them must preserve behavior,
    # and this pins the intended sharing.
    assert (
        _APPLY_DISPATCH["bootstrap_oracle"]
        is _APPLY_DISPATCH["oracle_report"]
        is _APPLY_DISPATCH["oracle_commit"]
    )


def test_teeth_unmapped_action_raises_unknown_in_apply_one():
    # TEETH (dispatch fallthrough): call _apply_one directly with an action that
    # has no dispatch entry. This exercises the dict-miss branch in isolation
    # (the public API would reject earlier at _require_action). Confirms a dropped
    # entry degrades to a hard "unknown action" reject, never a silent no-op.
    import pytest as _pytest

    from src.integration.zusd_monetary_bridge import _apply_one, init_monetary_state

    cfg = _cfg()
    with _pytest.raises(ValueError, match=r"^unknown action: not_a_real_action$"):
        _apply_one(
            config=cfg,
            balances=BalanceTable(),
            monetary_state=init_monetary_state(cfg),
            op=_op("not_a_real_action", 1),
            action="not_a_real_action",
            sender=ALICE,
            native_sender=ALICE_RAW,
            zusd_asset=cfg.zusd_asset,
            sp_pubkey=_sp(cfg),
        )


def test_teeth_owner_threading_first_deposit_initializes_owner():
    # TEETH (shared owner-resolution threading — the #1 refactor trap): the
    # owner-init side effect of the FIRST deposit_collateral on a fresh vault must
    # flow into the persisted next_state. If _apply_deposit_collateral forgot to
    # thread the resolved owner into state_from(owner=...), the vault would
    # persist vault_owner_pubkey=None and the very next owner-gated op (mint)
    # would wrongly reject with "vault owner not initialized".
    ctx = _bootstrapped()
    ctx.advance([_op("deposit_collateral", 1, amount_e8=20 * E8)], sender=ALICE)
    assert ctx.zusd.vault_owner_pubkey == ALICE
    # mint must now succeed against the threaded owner (would reject if owner=None).
    r = ctx.advance([_op("mint_zusd", 2, amount_e8=100 * E8)], sender=ALICE)
    assert r.zusd_state.vault_owner_pubkey == ALICE
    assert _last_effect(r)["event"] == "zusd_minted"


def test_teeth_redeem_validates_balance_before_step_and_credit():
    # TEETH (validate-before-mutate on redeem): _apply_redeem_zusd checks the
    # wallet balance BEFORE the core step and BEFORE it subtracts zUSD / credits
    # native collateral. If a refactor moved that balance guard after the
    # subtract, the underflow would raise BalanceTable's "Insufficient balance:
    # ..." instead of this bridge guard, flipping the exact error string below.
    # (The 3-way `result.effects is None` disjunct in redeem/liquidate is
    # unreachable via _step_python -- ok=True always carries non-None effects --
    # so it is intentionally NOT asserted here; it cannot bite without mocking.)
    ctx = _vault_open()
    _assert_reject_noop(
        ctx,
        [_op("redeem_zusd", 3, amount_e8=999 * E8)],
        sender=ALICE,
        error="zusd op[0] insufficient zUSD balance",
    )
