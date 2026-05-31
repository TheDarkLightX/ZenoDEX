"""CBC_CORE_V0 (Prompt 5): zUSD oracle-commit-MCR ESSO-step <-> running-impl differential.

Companion to `test_zusd_redeem_selector_step_differential.py`. Pins the verified
ESSO *step* semantics (codegen'd native adapter
`src/kernels/python/zusd_multi_oracle_commit_mcr_v1_native_adapter.py`, checked by
`ESSO verify-shell` against the kernel `zusd_multi_oracle_commit_mcr_v1`) to the
running `src.core.zusd_multi_oracle_commit_mcr.check_multi_oracle_commit_mcr`.

This kernel decides whether each vault stays MCR-OK at a *pending* committed oracle
price (the recovery/oracle-commit gate). For the same inputs both must AGREE on the
per-vault MCR-ok flags and the aggregate `mcr_ok_at_pending`. There is no semantic
reject for structurally-valid inputs (the gate always evaluates), so the domain is
restricted to valid inputs (non-negative price/vaults, positive mcr) — the running
impl validates and raises on the rest while the bare adapter does not, so those are
not a meaningful parity comparison. `tested_refinement`, not a machine proof.
"""

from __future__ import annotations

import random
import sys
from pathlib import Path
from types import ModuleType, SimpleNamespace

REPO = Path(__file__).resolve().parents[2]
if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))

from src.core.zusd_multi_oracle_commit_mcr import check_multi_oracle_commit_mcr  # noqa: E402

E8 = 100_000_000


def _install_fake_interpreter(monkeypatch):
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
    return adapter.apply(SimpleNamespace(tag="evaluate_multi_oracle_commit_mcr", args={}))


def _running_step(state: dict):
    try:
        out = check_multi_oracle_commit_mcr(
            price_pending_e8=state["price_pending_e8"],
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
            f"running REJECTED but adapter accepted for {state}"
        )
        return
    assert isinstance(adapter_res, interp_mod.StepOk), (
        f"running ACCEPTED but adapter errored for {state}: {getattr(adapter_res, 'code', '?')}"
    )
    eff = dict(adapter_res.effects)
    assert eff["vault_a_mcr_ok"] == rv.vault_a_mcr_ok, state
    assert eff["vault_b_mcr_ok"] == rv.vault_b_mcr_ok, state
    assert eff["mcr_ok_at_pending"] == rv.mcr_ok_at_pending, state


def _base_state() -> dict:
    return {
        "price_pending_e8": 100 * E8,
        "mcr_bps": 11_000,
        "vault_a_collateral_e8": 2 * E8,
        "vault_a_debt_e8": 150 * E8,
        "vault_b_collateral_e8": 2 * E8,
        "vault_b_debt_e8": 100 * E8,
    }


def test_oracle_commit_mcr_step_differential_deterministic(monkeypatch):
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import (  # noqa: E402
        zusd_multi_oracle_commit_mcr_v1_native_adapter as module,
    )

    cases: list[dict] = []
    cases.append(_base_state())  # both ok at base price
    one_fails = _base_state()
    one_fails.update(price_pending_e8=50 * E8, vault_b_debt_e8=80 * E8)
    cases.append(one_fails)  # depeg: one vault drops below MCR
    both_fail = _base_state()
    both_fail.update(price_pending_e8=1 * E8)  # deep depeg -> both under MCR
    cases.append(both_fail)
    zero_debt = _base_state()
    zero_debt.update(vault_a_debt_e8=0, vault_b_debt_e8=0)  # debt 0 -> trivially ok
    cases.append(zero_debt)
    price_zero = _base_state()
    price_zero.update(price_pending_e8=0)  # price 0 + nonzero debt -> both fail
    cases.append(price_zero)

    for state in cases:
        _assert_agree(_running_step(state), _adapter_step(module, state), interp_mod, state)


def test_oracle_commit_mcr_step_differential_randomized(monkeypatch):
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.kernels.python import (  # noqa: E402
        zusd_multi_oracle_commit_mcr_v1_native_adapter as module,
    )

    rng = random.Random(20260531)
    all_ok = 0
    not_ok = 0
    for _ in range(500):
        state = {
            "price_pending_e8": rng.randint(0, 200) * E8,
            "mcr_bps": rng.randint(10_000, 16_000),
            "vault_a_collateral_e8": rng.randint(0, 6) * E8,
            "vault_a_debt_e8": rng.randint(0, 400) * E8,
            "vault_b_collateral_e8": rng.randint(0, 6) * E8,
            "vault_b_debt_e8": rng.randint(0, 400) * E8,
        }
        running = _running_step(state)
        adapter_res = _adapter_step(module, state)
        _assert_agree(running, adapter_res, interp_mod, state)
        if running[0] == "ok":
            if running[1].mcr_ok_at_pending:
                all_ok += 1
            else:
                not_ok += 1

    # Both the all-vaults-OK and the at-least-one-fails branches must be exercised
    # (otherwise the differential would be vacuous on the MCR decision).
    assert all_ok > 0 and not_ok > 0, f"non-exercising corpus: all_ok={all_ok} not_ok={not_ok}"
