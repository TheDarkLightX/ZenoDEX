"""Refinement checks: the v3 native adapter vs its generated Python reference.

The reference model is generated from `src/kernels/dex/perp_epoch_isolated_v3.yaml`
by an optional kernel-spec toolchain vendored under `external/`.  The native
functional core is now deliberately stricter at one named product boundary:
a published price must settle before epoch advancement.

Accordingly this suite proves exact parity on the common admitted domain and
keeps the stale generated-reference behavior as an explicit release blocker.
It must return to total equality after the source model and reference are
regenerated.
"""

from __future__ import annotations

import hashlib
import importlib.util
import random
import re
import sys
from pathlib import Path
from typing import Any

import pytest

from src.core.perp_epoch import (
    perp_epoch_isolated_v3_native_apply,
    perp_epoch_isolated_v3_native_initial_state,
)
from src.core.perp_v2 import Action, ActionParams

EXPECTED_MODEL_SOURCE_SHA256 = (
    "1bf50a8693f7b83a846b9c6bacf918e604be3657e7138691b0a0aaf8fa3a8990"
)
EXPECTED_IR_HASH = (
    "sha256:23a9b8ec0233f3514301be3d347c6f3623db0876559efc00d904d5b0786a0cfe"
)
FORMAL_PROMOTION_BLOCKER = "PERP-PHASE-001"


def _import_generated_ref() -> Any:
    root = Path(__file__).resolve().parents[3]
    ref_path = root / "generated" / "perp_python" / "perp_epoch_isolated_v3_ref.py"
    if not ref_path.exists():
        pytest.skip(f"generated ref not found at {ref_path}", allow_module_level=True)

    module_name = "generated.perp_python.perp_epoch_isolated_v3_ref"
    spec = importlib.util.spec_from_file_location(module_name, ref_path)
    assert spec and spec.loader, f"could not load spec from {ref_path}"
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


REF = _import_generated_ref()


def test_v3_generated_reference_is_bound_to_current_esso_source() -> None:
    root = Path(__file__).resolve().parents[3]
    model = root / "src" / "kernels" / "dex" / "perp_epoch_isolated_v3.yaml"
    reference = (
        root / "generated" / "perp_python" / "perp_epoch_isolated_v3_ref.py"
    )
    source = reference.read_text(encoding="utf-8")
    match = re.search(r"^IR hash: (sha256:[0-9a-f]{64})$", source, re.MULTILINE)

    assert hashlib.sha256(model.read_bytes()).hexdigest() == (
        EXPECTED_MODEL_SOURCE_SHA256
    )
    assert match is not None
    assert match.group(1) == EXPECTED_IR_HASH


def _to_ref_cmd(params: ActionParams) -> Any:
    tag = params.action.value
    args: dict[str, Any] = {}

    if params.action is Action.ADVANCE_EPOCH:
        args["delta"] = int(params.delta)
    elif params.action is Action.PUBLISH_CLEARING_PRICE:
        args["price_e8"] = int(params.price_e8)
    elif params.action is Action.DEPOSIT_COLLATERAL:
        args["amount"] = int(params.amount)
        args["auth_ok"] = bool(params.auth_ok)
    elif params.action is Action.WITHDRAW_COLLATERAL:
        args["amount"] = int(params.amount)
        args["auth_ok"] = bool(params.auth_ok)
    elif params.action is Action.SET_POSITION:
        args["new_position_base"] = int(params.new_position_base)
        args["auth_ok"] = bool(params.auth_ok)
    elif params.action is Action.CLEAR_BREAKER:
        args["auth_ok"] = bool(params.auth_ok)
    elif params.action is Action.APPLY_FUNDING:
        args["new_rate_bps"] = int(params.new_rate_bps)
        args["auth_ok"] = bool(params.auth_ok)
    elif params.action is Action.DEPOSIT_INSURANCE:
        args["amount"] = int(params.amount)
    elif params.action is Action.APPLY_INSURANCE_CLAIM:
        args["claim_amount"] = int(params.claim_amount)
        args["auth_ok"] = bool(params.auth_ok)
    elif params.action is Action.SETTLE_EPOCH:
        args = {}
    else:
        raise AssertionError(f"unhandled action in parity test: {params.action}")

    return REF.Command(tag=tag, args=args)


def _random_action_params(rng: random.Random) -> ActionParams:
    action = rng.choice(
        [
            Action.ADVANCE_EPOCH,
            Action.PUBLISH_CLEARING_PRICE,
            Action.SETTLE_EPOCH,
            Action.DEPOSIT_COLLATERAL,
            Action.WITHDRAW_COLLATERAL,
            Action.SET_POSITION,
            Action.CLEAR_BREAKER,
            Action.APPLY_FUNDING,
            Action.DEPOSIT_INSURANCE,
            Action.APPLY_INSURANCE_CLAIM,
        ]
    )

    if action is Action.ADVANCE_EPOCH:
        return ActionParams(action=action, delta=rng.randint(1, 3))
    if action is Action.PUBLISH_CLEARING_PRICE:
        return ActionParams(action=action, price_e8=rng.randint(1, 2_000_000_000))
    if action is Action.DEPOSIT_COLLATERAL:
        return ActionParams(action=action, amount=rng.randint(1, 50_000), auth_ok=True)
    if action is Action.WITHDRAW_COLLATERAL:
        return ActionParams(action=action, amount=rng.randint(1, 50_000), auth_ok=True)
    if action is Action.SET_POSITION:
        return ActionParams(action=action, new_position_base=rng.randint(-1000, 1000), auth_ok=True)
    if action is Action.CLEAR_BREAKER:
        return ActionParams(action=action, auth_ok=True)
    if action is Action.APPLY_FUNDING:
        return ActionParams(action=action, new_rate_bps=rng.randint(-100, 100), auth_ok=True)
    if action is Action.DEPOSIT_INSURANCE:
        return ActionParams(action=action, amount=rng.randint(1, 100_000))
    if action is Action.APPLY_INSURANCE_CLAIM:
        return ActionParams(action=action, claim_amount=rng.randint(1, 50_000), auth_ok=True)
    if action is Action.SETTLE_EPOCH:
        return ActionParams(action=action)

    raise AssertionError("unreachable")


class TestPerpV3AdapterParityWithGeneratedRef:
    def test_initial_state_matches(self) -> None:
        ours = perp_epoch_isolated_v3_native_initial_state()
        ref = REF.init_state()
        assert ours == vars(ref)

    def test_random_trace_parity_on_common_admitted_domain(self) -> None:
        rng = random.Random(0)
        ours = perp_epoch_isolated_v3_native_initial_state()
        ref = REF.init_state()

        ours = {
            **ours,
            "oracle_seen": True,
            "oracle_last_update_epoch": 0,
            "index_price_e8": 100_000_000,
        }
        ref = REF.State(
            **{
                **vars(ref),
                "oracle_seen": True,
                "oracle_last_update_epoch": 0,
                "index_price_e8": 100_000_000,
            }
        )

        for _ in range(500):
            params = _random_action_params(rng)
            # The pinned source model remains permissive for this one named
            # lifecycle trace.  Skip it here and assert the divergence below.
            if params.action is Action.ADVANCE_EPOCH and ours["epoch_phase"] == 1:
                continue
            command = _to_ref_cmd(params)
            our_res = perp_epoch_isolated_v3_native_apply(
                state=ours,
                action=command.tag,
                params=command.args,
            )
            ref_res = REF.step(ref, command)

            assert our_res.ok == ref_res.ok

            if not our_res.ok:
                continue

            assert our_res.state is not None
            assert our_res.effects is not None
            assert ref_res.state is not None
            assert ref_res.effects is not None

            assert our_res.state == vars(ref_res.state)
            assert our_res.effects == dict(ref_res.effects)

            ours = our_res.state
            ref = ref_res.state

    def test_unsettled_epoch_advance_is_an_explicit_formal_promotion_blocker(self) -> None:
        state = {
            **perp_epoch_isolated_v3_native_initial_state(),
            "now_epoch": 5,
            "epoch_phase": 1,
            "clearing_price_seen": True,
            "clearing_price_epoch": 5,
            "clearing_price_e8": 100_000_000,
            "oracle_seen": True,
            "oracle_last_update_epoch": 4,
            "index_price_e8": 100_000_000,
        }
        command = REF.Command(tag="advance_epoch", args={"delta": 1})

        native = perp_epoch_isolated_v3_native_apply(
            state=state,
            action=command.tag,
            params=command.args,
        )
        reference = REF.step(REF.State(**state), command)

        assert FORMAL_PROMOTION_BLOCKER == "PERP-PHASE-001"
        assert native.ok is False
        assert native.state is None
        assert native.effects is None
        assert reference.ok is True
