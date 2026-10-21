"""Parity check: `src/core/vault.py` vs generated ref for the (bounded) vault kernel.

Important: the generated ref model has *small bounded domains* (e.g. `staked_lp_shares <= 100`).
We treat this as a bounded proof/reference model; parity claims here are only about behavior
within that domain, not about unbounded production-scale limits.
"""

from __future__ import annotations

import importlib.util
import random
import sys
from dataclasses import fields
from pathlib import Path
from typing import Any

import pytest

from src.core.vault import VaultCommand, VaultState, init_vault_state, step


def _import_generated_ref() -> Any:
    root = Path(__file__).resolve().parents[2]
    ref_path = root / "generated" / "vault_python" / "vault_manager_ref.py"
    if not ref_path.exists():
        pytest.skip(f"generated ref not found at {ref_path}", allow_module_level=True)

    module_name = "generated.vault_python.vault_manager_ref"
    spec = importlib.util.spec_from_file_location(module_name, ref_path)
    assert spec and spec.loader, f"could not load spec from {ref_path}"
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


REF = _import_generated_ref()


def _field_dict(value: Any) -> dict[str, Any]:
    return {field.name: getattr(value, field.name) for field in fields(value)}


def _to_ref_state(s: VaultState):
    return REF.State(**_field_dict(s))


def _to_ref_cmd(cmd: VaultCommand):
    return REF.Command(tag=cmd.tag, args=dict(cmd.args))


def _random_cmd(rng: random.Random, s: VaultState) -> VaultCommand:
    # Keep within the bounded ref domain so parity is meaningful:
    # pending_rewards, reward_balance <= 1_000_000; staked_lp_shares <= 100.
    MAX_REWARD = 1_000_000
    MAX_STAKE = 100

    candidates: list[VaultCommand] = []

    # Deposit (bounded): keep reward_balance <= 1_000_000.
    room = int(MAX_REWARD) - int(s.reward_balance)
    if room >= 1:
        amt = rng.randint(1, min(10_000, room))
        candidates.append(VaultCommand(tag="deposit_rewards", args={"amount": amt}))

    # Stake (bounded): keep staked_lp_shares <= 100.
    stake_room = int(MAX_STAKE) - int(s.staked_lp_shares)
    if stake_room >= 1:
        amt = rng.randint(1, min(100, stake_room))
        candidates.append(VaultCommand(tag="stake", args={"amount": amt}))

    # Unstake (bounded): only if some stake exists.
    if int(s.staked_lp_shares) >= 1:
        amt = rng.randint(1, min(100, int(s.staked_lp_shares)))
        candidates.append(VaultCommand(tag="unstake", args={"amount": amt}))

    # Harvest is always a syntactically valid command; guards decide feasibility.
    entry_acc = rng.randint(0, max(0, int(s.acc_reward_per_share)))
    candidates.append(VaultCommand(tag="harvest", args={"entry_acc": entry_acc}))

    assert candidates
    return rng.choice(candidates)


class TestVaultParityWithGeneratedRef:
    def test_initial_state_matches(self) -> None:
        ours = init_vault_state()
        ref = REF.init_state()
        assert _field_dict(_to_ref_state(ours)) == _field_dict(ref)

    @pytest.mark.parametrize(
        "amount,within_ref_domain,reason",
        [
            (0, False, "just below min=1"),
            (1, True, "at min"),
            (2, True, "just above min"),
            (10_000, True, "at max (ref)"),
            (10_001, False, "just above max (ref)"),
        ],
    )
    def test_bva_deposit_amount_vs_ref_domain(self, amount: int, within_ref_domain: bool, reason: str) -> None:
        ours = init_vault_state()
        ref = REF.init_state()
        cmd = VaultCommand(tag="deposit_rewards", args={"amount": amount})

        our_res = step(ours, cmd)
        ref_res = REF.step(ref, _to_ref_cmd(cmd))

        if within_ref_domain:
            assert our_res.ok == ref_res.ok, reason
            if our_res.ok:
                assert _field_dict(our_res.state) == _field_dict(ref_res.state)
                assert dict(our_res.effects or {}) == dict(ref_res.effects or {})
        else:
            # Out-of-domain for the bounded ref: assert the ref rejects, but do not require the
            # unbounded runtime to match.
            assert not ref_res.ok, reason

    def test_random_trace_parity_bounded(self) -> None:
        rng = random.Random(0)
        ours = init_vault_state()
        ref = REF.init_state()

        for _ in range(500):
            cmd = _random_cmd(rng, ours)

            our_res = step(ours, cmd)
            ref_res = REF.step(ref, _to_ref_cmd(cmd))

            assert our_res.ok == ref_res.ok

            if not our_res.ok:
                continue

            assert our_res.state is not None
            assert our_res.effects is not None
            assert ref_res.state is not None
            assert ref_res.effects is not None

            assert _field_dict(our_res.state) == _field_dict(ref_res.state)
            assert dict(our_res.effects) == dict(ref_res.effects)

            ours = our_res.state
            ref = ref_res.state
