#!/usr/bin/env python3
"""Render Python reference vectors for the native custody coordinator.

Replay with --check; omit it to regenerate. Synthetic contexts grant no
receipt, profile, publication, or replay-consumption authority.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import replace
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core.asset_lane_coordinator_v1 import compose_asset_lane_single_v1  # noqa: E402
from src.core.asset_lane_projection_v1 import (  # noqa: E402
    AssetLaneCompositionAcceptedV1,
    AssetLaneCoordinatorContextV1,
)
from src.core.asset_transfer_lane_module_custody_v1 import (  # noqa: E402
    transition_asset_transfer_lane_module_custody_v1,
)
from src.core.asset_transfer_lane_module_v1 import (  # noqa: E402
    AssetTransferLaneModuleAcceptedV1,
    AssetTransferLaneModuleInputV1,
)
from src.core.asset_transfer_types_v1 import AssetTransferRejectedV1  # noqa: E402
from src.core.global_settlement_types_v1 import (  # noqa: E402
    EconomicAmountV1,
    canonical_global_bytes_v1,
)
from tests.core.test_asset_transfer_lane_module_custody_v1 import (  # noqa: E402
    MAX_ATOMS,
    _custody_input,
    _high_balance_input,
)
from tests.core.test_asset_transfer_lane_module_v1 import _coordinator_context  # noqa: E402

FIXTURE = ROOT / "tests/data/asset_lane_custody_coordinator_v1_golden.json"
SOURCES = (
    "tools/render_asset_lane_custody_coordinator_v1_golden.py",
    "src/core/asset_transfer_lane_module_custody_v1.py",
    "src/core/asset_transfer_lane_module_v1.py",
    "src/core/asset_transfer_module_v1.py",
    "src/core/asset_transfer_types_v1.py",
    "src/core/asset_lane_coordinator_v1.py",
    "src/core/asset_lane_projection_v1.py",
    "src/core/global_economic_proof_v1.py",
    "src/core/global_settlement_types_v1.py",
    "tests/core/test_asset_transfer_lane_module_custody_v1.py",
    "tests/core/test_asset_transfer_lane_module_v1.py",
)
WIRE_SCHEMA = "zenodex/asset-lane-coordinator-guest-input/v1"


def _wire(module_input, context) -> dict[str, object]:
    return {
        "schema": WIRE_SCHEMA,
        "module_input": module_input.to_canonical(),
        "coordinator_context": context,
    }


def _accepted_case(name, module_input, context):
    module = transition_asset_transfer_lane_module_custody_v1(module_input)
    if type(module) is not AssetTransferLaneModuleAcceptedV1:
        raise ValueError(f"{name}: Python module rejected positive control")
    lane = compose_asset_lane_single_v1(
        context, module.module_journal, module.private_port, module.effects
    )
    if type(lane) is not AssetLaneCompositionAcceptedV1:
        raise ValueError(f"{name}: Python coordinator rejected positive control")
    command = module_input.command
    policy = next(p for p in module_input.pre_state.policies if p.asset == command.asset)
    # An independent integer-account oracle checks movements, including fee aliases.
    balances = {row.key: row.amount_atoms for row in module_input.pre_state.balances}
    for owner, delta in (
        (command.sender, -command.amount_atoms - policy.transfer_fee_atoms),
        (command.recipient, command.amount_atoms),
        (policy.fee_owner, policy.transfer_fee_atoms),
    ):
        key = (command.asset, owner, "accounts")
        balances[key] = balances.get(key, 0) + delta
    balances = {key: value for key, value in balances.items() if value}
    if balances != {row.key: row.amount_atoms for row in module.post_state.balances}:
        raise ValueError(f"{name}: independent account oracle disagrees")
    total = sum(
        row.amount_atoms
        for row in (*module_input.pre_state.balances, *module_input.custody)
        if row.asset == command.asset
    )
    if lane.effects.asset_conservation[0].owned_and_custodied_post_atoms != total:
        raise ValueError(f"{name}: independent physical total disagrees")
    wire = _wire(module_input, context)
    return {
        "name": name,
        "input": wire,
        "input_utf8": canonical_global_bytes_v1(wire).decode(),
        "module_accepted": {
            "statement_root": module.statement_root,
            "post_state": module.post_state,
            "effects": module.effects,
            "private_port": module.private_port,
            "module_journal": module.module_journal,
        },
        "lane_accepted": {
            "post_state": lane.post_state,
            "effects": lane.effects,
            "lane_journal": lane.lane_journal,
        },
        "module_journal_utf8": canonical_global_bytes_v1(module.module_journal).decode(),
        "lane_journal_utf8": canonical_global_bytes_v1(lane.lane_journal).decode(),
        "expected_total": str(total),
    }, module


def positive_inputs() -> list[tuple[str, AssetTransferLaneModuleInputV1]]:
    inputs = [
        (f"custody_{atoms}", _custody_input(atoms))
        for atoms in (0, 1, 7, 1 << 127, MAX_ATOMS - 116, MAX_ATOMS - 115)
    ]
    inputs.append(("high_account_small_delta", _high_balance_input()))
    inputs.extend(
        (f"fee_owner_{owner}", _custody_input(7, fee_owner=owner))
        for owner in ("alice", "bob", "treasury")
    )
    original = _custody_input(7)
    state = original.pre_state
    foreign = replace(
        original,
        pre_state=replace(
            state,
            policies=(replace(state.policies[0], asset="EUR"), *state.policies),
            supplies=(replace(state.supplies[0], asset="EUR", amount_atoms=9), *state.supplies),
        ),
        custody=(EconomicAmountV1("other-vault", "EUR", "other", 9), *original.custody),
    )
    inputs.append(("foreign_asset_custody_frame", foreign))
    return inputs


def history() -> list[dict[str, object]]:
    first_input = _custody_input(7)
    first, accepted = _accepted_case("first", first_input, _coordinator_context())
    occurrence = f"0x{44:064x}"
    second_input = replace(
        first_input,
        pre_state=accepted.post_state,
        context=replace(first_input.context, command_occurrence_id=occurrence),
        command=replace(first_input.command, amount_atoms=1),
    )
    context: AssetLaneCoordinatorContextV1 = replace(
        _coordinator_context(), command_occurrence_id=occurrence
    )
    rejected_input = replace(second_input, command=replace(second_input.command, amount_atoms=0))
    rejected = transition_asset_transfer_lane_module_custody_v1(rejected_input)
    if type(rejected) is not AssetTransferRejectedV1 or rejected.code.value != "ZERO_AMOUNT":
        raise ValueError("history rejection control disagrees")
    if not rejected.effects.is_empty or rejected.pre_state_root != rejected.post_state_root:
        raise ValueError("history rejection is not a logical no-op")
    rejection = {
        "name": "rejected_between_transfers",
        "input": _wire(rejected_input, context),
        "reject_code": rejected.code.value,
        "unchanged_module_state_root": rejected.pre_state_root,
    }
    second, _ = _accepted_case("second_after_rejection", second_input, context)
    return [first, rejection, second]


def render() -> str:
    payload = {
        "schema": "zenodex/asset-lane-custody-coordinator-golden/v1",
        "authority": "NONE",
        "cases": [
            _accepted_case(name, value, _coordinator_context())[0]
            for name, value in positive_inputs()
        ],
        "history": history(),
        "source_sha256": {
            name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in SOURCES
        },
    }
    return (
        json.dumps(json.loads(canonical_global_bytes_v1(payload)), sort_keys=True, indent=2) + "\n"
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    content = render()
    if args.check:
        if FIXTURE.read_text() != content:
            raise SystemExit("custody coordinator fixture is stale")
    else:
        FIXTURE.write_text(content)


if __name__ == "__main__":
    main()
