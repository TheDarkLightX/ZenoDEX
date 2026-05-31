"""CBC_CORE_V0 (Prompt 5): zUSD redeem-selector ESSO-step <-> running-impl differential.

Pins the verified ESSO *step* semantics (the codegen'd native adapter
`src/kernels/python/zusd_multi_redeem_selector_v1_native_adapter.py`, which
`ESSO verify-shell` checks against the kernel `zusd_multi_redeem_selector_v1`) to
the *running* selector `src.core.zusd_multi_redeem_selector.select_multi_redeem_vault`.

For the same inputs both must AGREE on:
  - accept vs reject  (running raises ValueError / tiny-gross  <->  adapter StepError),
  - gross collateral, per-vault candidate-ok, per-vault headroom,
  - the selected vault, with the running `"a"/"b"/None` mapped to the adapter's
    `selection_ok` + `"VaultA"/"VaultB"`.

This is a `tested_refinement` (a differential), NOT a machine proof binding the two
implementations. The domain is restricted to structurally-valid inputs (positive
amount/price/mcr, non-negative vault fields): the running impl validates these and
raises, while the bare adapter does not, so out-of-domain inputs are not a
meaningful parity comparison and are excluded by construction.

Scope note: this worktree ships zUSD ESSO kernels + native adapters only for
`redeem_selector` and `oracle_commit_mcr` (there is no liquidation/mint/repay
kernel), so this is the value-bearing redemption slice of the step<->adapter gap.
"""

from __future__ import annotations

import random
import sys
from pathlib import Path
from types import ModuleType, SimpleNamespace

import pytest

REPO = Path(__file__).resolve().parents[2]
if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))

from src.core.zusd_multi_redeem_selector import select_multi_redeem_vault  # noqa: E402

E8 = 100_000_000
_SELECTED = {"a": "VaultA", "b": "VaultB"}


def _install_fake_interpreter(monkeypatch):
    """Provide the `ESSO.kernel.interpreter` StepOk/StepError the adapter imports."""
    esso_mod = ModuleType("ESSO")
    kernel_mod = ModuleType("ESSO.kernel")
    interp_mod = ModuleType("ESSO.kernel.interpreter")

    class StepOk:
        def __init__(self, *, state, effects):
            self.state = state
            self.effects = effects

    class StepError:
        def __init__(self, *, code: str, message: str):
            self.code = code
            self.message = message

    interp_mod.StepOk = StepOk
    interp_mod.StepError = StepError
    kernel_mod.interpreter = interp_mod
    esso_mod.kernel = kernel_mod
    monkeypatch.setitem(sys.modules, "ESSO", esso_mod)
    monkeypatch.setitem(sys.modules, "ESSO.kernel", kernel_mod)
    monkeypatch.setitem(sys.modules, "ESSO.kernel.interpreter", interp_mod)
    return interp_mod


def _adapter_step(module, state: dict) -> object:
    adapter = module.make_adapter(ir={"schema": "fake"})
    adapter.reset(state=dict(state))
    return adapter.apply(SimpleNamespace(tag="select_redeem_vault", args={}))


def _running_step(state: dict):
    """Return ('ok', Outcome) or ('err', message) for the running selector."""
    try:
        out = select_multi_redeem_vault(
            amount_e8=state["amount_e8"],
            price_e8=state["price_e8"],
            mcr_bps=state["mcr_bps"],
            vault_a_collateral_e8=state["vault_a_collateral_e8"],
            vault_a_debt_e8=state["vault_a_debt_e8"],
            vault_b_collateral_e8=state["vault_b_collateral_e8"],
            vault_b_debt_e8=state["vault_b_debt_e8"],
        )
        return ("ok", out)
    except ValueError as exc:
        return ("err", str(exc))


def _assert_agree(running, adapter_res, interp_mod, state: dict) -> None:
    kind, rv = running
    if kind == "err":
        assert isinstance(adapter_res, interp_mod.StepError), (
            f"running REJECTED but adapter accepted for {state}: "
            f"adapter={getattr(adapter_res, 'effects', adapter_res)}"
        )
        return
    assert isinstance(adapter_res, interp_mod.StepOk), (
        f"running ACCEPTED but adapter errored for {state}: "
        f"{getattr(adapter_res, 'code', '?')}"
    )
    eff = dict(adapter_res.effects)
    assert eff["gross_collateral_e8"] == rv.gross_collateral_e8, state
    assert eff["candidate_a_ok"] == rv.candidate_a_ok, state
    assert eff["candidate_b_ok"] == rv.candidate_b_ok, state
    assert eff["headroom_a_before_e8"] == rv.headroom_a_before_e8, state
    assert eff["headroom_b_before_e8"] == rv.headroom_b_before_e8, state
    if rv.selected_vault is None:
        assert eff.get("selection_ok") is False, (
            f"running selected nothing but adapter selected for {state}: {eff}"
        )
    else:
        assert eff.get("selection_ok") is True, state
        assert eff["selected_vault"] == _SELECTED[rv.selected_vault], (
            f"selected-vault disagreement for {state}: "
            f"running={rv.selected_vault} adapter={eff['selected_vault']}"
        )


def _base_state() -> dict:
    return {
        "amount_e8": 50 * E8,
        "price_e8": 100 * E8,
        "mcr_bps": 11_000,
        "vault_a_collateral_e8": 5 * E8,
        "vault_a_debt_e8": 200 * E8,
        "vault_b_collateral_e8": 5 * E8,
        "vault_b_debt_e8": 300 * E8,
    }


def test_redeem_selector_step_differential_deterministic(monkeypatch):
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import (  # noqa: E402
        zusd_multi_redeem_selector_v1_native_adapter as module,
    )

    cases: list[dict] = []
    # Both vaults eligible -> selection by smaller headroom (here VaultB).
    cases.append(_base_state())
    # Tie on headroom -> deterministic VaultA.
    tie = _base_state()
    tie.update(
        vault_a_collateral_e8=4 * E8,
        vault_a_debt_e8=200 * E8,
        vault_b_collateral_e8=4 * E8,
        vault_b_debt_e8=200 * E8,
    )
    cases.append(tie)
    # Only one vault eligible (B has too little collateral for the gross draw).
    one = _base_state()
    one.update(vault_b_collateral_e8=0, vault_b_debt_e8=0)
    cases.append(one)
    # No eligible vault (both under-collateralized after the draw).
    none_ok = _base_state()
    none_ok.update(
        vault_a_collateral_e8=1,
        vault_b_collateral_e8=1,
    )
    cases.append(none_ok)
    # Tiny gross at extreme price -> both REJECT (running ValueError / adapter GuardFalse).
    tiny = _base_state()
    tiny.update(amount_e8=1, price_e8=10**30)
    cases.append(tiny)

    for state in cases:
        _assert_agree(_running_step(state), _adapter_step(module, state), interp_mod, state)


def test_redeem_selector_step_differential_randomized(monkeypatch):
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import (  # noqa: E402
        zusd_multi_redeem_selector_v1_native_adapter as module,
    )

    rng = random.Random(20260531)
    accepts = 0
    rejects = 0
    selected = 0
    for _ in range(500):
        if rng.random() < 0.18:
            # Tiny-gross / extreme-price territory: exercises the REJECT path
            # (gross_collateral_e8 == 0 -> running ValueError / adapter GuardFalse).
            amount_e8 = rng.randint(1, 1_000)
            price_e8 = rng.choice([rng.randint(1, 200) * E8, 10**24])
        else:
            amount_e8 = rng.randint(1, 80) * E8
            price_e8 = rng.randint(1, 200) * E8
        state = {
            "amount_e8": amount_e8,
            "price_e8": price_e8,
            "mcr_bps": rng.randint(10_000, 16_000),
            "vault_a_collateral_e8": rng.randint(0, 12) * E8,
            "vault_a_debt_e8": rng.randint(0, 600) * E8,
            "vault_b_collateral_e8": rng.randint(0, 12) * E8,
            "vault_b_debt_e8": rng.randint(0, 600) * E8,
        }
        running = _running_step(state)
        adapter_res = _adapter_step(module, state)
        _assert_agree(running, adapter_res, interp_mod, state)
        if running[0] == "err":
            rejects += 1
        else:
            accepts += 1
            if running[1].selected_vault is not None:
                selected += 1

    # The corpus must actually exercise accepts, rejects, and real vault selections
    # (otherwise the differential would be vacuous).
    assert accepts > 0 and rejects > 0 and selected > 0, (
        f"non-exercising corpus: accepts={accepts} rejects={rejects} selected={selected}"
    )
