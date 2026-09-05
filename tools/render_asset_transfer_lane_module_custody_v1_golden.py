#!/usr/bin/env python3
"""Replay with --check; omit it to regenerate the pure successor vectors."""

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

from src.core.asset_transfer_lane_module_custody_v1 import (  # noqa: E402
    transition_asset_transfer_lane_module_custody_v1,
)
from src.core.asset_transfer_lane_module_v1 import AssetTransferLaneModuleAcceptedV1  # noqa: E402
from src.core.global_settlement_types_v1 import canonical_global_bytes_v1  # noqa: E402
from tests.core.test_asset_transfer_lane_module_custody_v1 import (  # noqa: E402
    MAX_ATOMS,
    _custody_input,
    _high_balance_input,
)
from tests.core.test_asset_transfer_lane_module_v1 import _coordinator_context  # noqa: E402
from tools.render_asset_transfer_global_allocation_v1_golden import _accepted_value  # noqa: E402

FIXTURE = ROOT / "tests/data/asset_transfer_lane_module_custody_v1_golden.json"
SOURCES = (
    "src/core/asset_transfer_lane_module_custody_v1.py",
    "src/core/asset_transfer_lane_module_v1.py",
    "zk/global_settlement_abi_v1/src/asset_transfer_lane_module_custody.rs",
    "zk/global_settlement_abi_v1/src/asset_transfer_lane_module.rs",
)


def _positive_case(module_input, name, expected_total):
    accepted = transition_asset_transfer_lane_module_custody_v1(module_input)
    if type(accepted) is not AssetTransferLaneModuleAcceptedV1:
        raise ValueError("positive successor input was rejected")
    row = accepted.effects.asset_conservation[0]
    if (
        row.owned_and_custodied_pre_atoms != expected_total
        or row.owned_and_custodied_post_atoms != expected_total
    ):
        raise ValueError("independent physical total disagrees")
    return {
        "name": name,
        "input": module_input.to_canonical(),
        "accepted": _accepted_value(accepted),
        "expected_total": str(expected_total),
    }


def render() -> str:
    cases = [
        _positive_case(_custody_input(atoms), f"custody_{atoms}", 115 + atoms)
        for atoms in (0, 1, 7, 1 << 127, MAX_ATOMS - 116, MAX_ATOMS - 115)
    ]
    for name, changes in (
        ("zero", {"amount_atoms": 0}),
        ("fee", {"max_fee_atoms": 1}),
        ("balance", {"amount_atoms": 1000}),
    ):
        module_input = _custody_input(7)
        module_input = replace(module_input, command=replace(module_input.command, **changes))
        result = transition_asset_transfer_lane_module_custody_v1(module_input)
        if isinstance(result, AssetTransferLaneModuleAcceptedV1):
            raise ValueError("negative successor input was accepted")
        expected = {
            "zero": "ZERO_AMOUNT",
            "fee": "FEE_LIMIT_EXCEEDED",
            "balance": "INSUFFICIENT_BALANCE",
        }[name]
        if result.code.value != expected:
            raise ValueError("independent rejection disagrees")
        cases.append({"name": name, "input": module_input.to_canonical(), "reject_code": expected})
    cases.append(_positive_case(_high_balance_input(), "high_account_small_delta", (1 << 127) + 15))
    overflow = _custody_input(MAX_ATOMS - 115)
    object.__setattr__(overflow.custody[0], "amount_atoms", MAX_ATOMS - 114)
    payload = json.loads(
        canonical_global_bytes_v1(
            {
                "cases": tuple(cases),
                "overflow_input": overflow.to_canonical(),
                "coordinator_context": _coordinator_context(),
            }
        )
    )
    payload.update(schema="zenodex/asset-transfer-lane-module-custody-golden/v1", authority="NONE")
    payload["source_sha256"] = {
        name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in SOURCES
    }
    return json.dumps(payload, sort_keys=True, indent=2) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    content = render()
    if args.check:
        if FIXTURE.read_text() != content:
            raise SystemExit("custody successor fixture is stale")
    else:
        FIXTURE.write_text(content)


if __name__ == "__main__":
    main()
