# [TESTER] v1
"""Production-readiness containment regression for mechanism-design finding
O-SS-06 / H-MD-SS-007 (CoW self-netting LP fee+spread capture).

CoW pair-netting (``swap_ordering == "cow_pair_netting_v1"``) fills matched
opposite-direction intents peer-to-peer at ``fee_paid == 0`` with no pool
interaction, so LPs earn neither fee nor spread on the netted volume
(experiments/mechanism_design_math_v1/wave1_spot_settlement/
test_cow_self_netting_capture.py). That ordering is EXPERIMENTAL and opt-in: the
authority settlement configs default to ``greedy_ab_refined`` and no deploy
config enables CoW. These tests LOCK IN that containment so the LP-capture path
cannot be silently enabled — they fail if CoW becomes a default, if a deploy
config selects it, or if the default ordering ever starts CoW-netting a matchable
pair.

Production posture only; this does not change settlement behavior.
"""

from __future__ import annotations

from pathlib import Path

from src.core.batch_clearing import compute_settlement
from src.core.dex import DexConfig
from src.integration.dex_engine import DexEngineConfig
from src.state.balances import BalanceTable
from src.state.intents import Intent, IntentKind
from src.state.lp import LPTable
from src.state.pools import PoolState, PoolStatus

_COW = "cow_pair_netting_v1"
_SAFE_DEFAULT = "greedy_ab_refined"
_REPO_ROOT = Path(__file__).resolve().parents[2]


def test_authority_config_defaults_use_safe_ordering_not_cow() -> None:
    """Both authority settlement config defaults route through the pool ordering,
    not the fee-free CoW netting ordering."""
    assert DexConfig().swap_ordering == _SAFE_DEFAULT
    assert DexConfig().swap_ordering != _COW
    assert DexEngineConfig().swap_ordering == _SAFE_DEFAULT
    assert DexEngineConfig().swap_ordering != _COW


def test_deploy_configs_do_not_enable_cow_netting() -> None:
    """No shipped deploy config selects the CoW pair-netting ordering."""
    deploy_dir = _REPO_ROOT / "config" / "deploy"
    yamls = sorted(deploy_dir.glob("*.yaml"))
    assert yamls, "expected deploy configs under config/deploy"
    for path in yamls:
        text = path.read_text(encoding="utf-8")
        assert _COW not in text, f"{path.name} must not enable CoW pair-netting ({_COW})"


def test_production_default_ordering_routes_matchable_pair_through_pool() -> None:
    """Behavioral containment: under the PRODUCTION DEFAULT ordering, a pair that
    WOULD CoW-net (matchable opposite exact-in swaps) is instead routed through the
    pool — no COW_NETTED fill, LPs earn the full fee, and pool reserves move. So
    the default makes the LP-capture mechanism inert, not merely unconfigured."""
    a0 = "0x" + "01" * 32
    a1 = "0x" + "02" * 32
    t_pk = "0x" + "11" * 48
    a_pk = "0x" + "22" * 48
    pid = "0x" + "aa" * 32

    def _iid(n: int) -> str:
        return "0x" + f"{n:064x}"

    def _pool() -> PoolState:
        return PoolState(
            pool_id=pid, asset0=a0, asset1=a1, reserve0=1_000_000, reserve1=1_000_000,
            fee_bps=30, lp_supply=0, status=PoolStatus.ACTIVE, created_at=0)

    def _swap(iid: str, sender: str, ai: str, ao: str, amt: int, mo: int) -> Intent:
        return Intent(
            module="TauSwap", version="0.1", kind=IntentKind.SWAP_EXACT_IN, intent_id=iid,
            sender_pubkey=sender, deadline=9999999999,
            fields={"pool_id": pid, "asset_in": ai, "asset_out": ao,
                    "amount_in": amt, "min_amount_out": mo})

    balances = BalanceTable()
    balances.set(t_pk, a0, 1_000_000)
    balances.set(a_pk, a1, 1_000_000)

    # A pair that DOES CoW-net under cow_pair_netting_v1 (see O-SS-06 evidence).
    intents = [
        _swap(_iid(1), t_pk, a0, a1, 100_000, 90_000),
        _swap(_iid(2), a_pk, a1, a0, 95_000, 90_000),
    ]

    settlement = compute_settlement(
        intents, {pid: _pool()}, balances, LPTable(),
        swap_ordering=DexConfig().swap_ordering,   # the production default
    )
    fills = [f for f in settlement.fills if f.action.value == "FILL"]

    assert [f.intent_id for f in fills] == [_iid(1), _iid(2)]      # both legs filled (non-vacuous)
    assert not any(f.reason == "COW_NETTED" for f in fills)        # no fee-free netting
    assert sum(int(f.fee_paid or 0) for f in fills) > 0            # LPs earn the fee
    assert settlement.reserve_deltas != []                        # pool reserves move

    # Positive control: the SAME pair DOES CoW-net under the opt-in ordering, so the
    # default-routing result above is a real containment, not a vacuously unmatchable
    # pair. (Confirms the witness exercises the live CoW path.)
    cow = compute_settlement(
        intents, {pid: _pool()}, balances, LPTable(), swap_ordering=_COW,
    )
    cow_fills = [f for f in cow.fills if f.action.value == "FILL"]
    assert [f.intent_id for f in cow_fills] == [_iid(1), _iid(2)]  # exactly both legs (non-vacuous)
    assert all(f.reason == "COW_NETTED" for f in cow_fills)        # the pair IS matchable
    assert sum(int(f.fee_paid or 0) for f in cow_fills) == 0       # ... fee-free under CoW
    assert cow.reserve_deltas == []                               # ... and bypasses the pool
