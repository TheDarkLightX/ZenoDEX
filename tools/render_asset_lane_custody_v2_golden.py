#!/usr/bin/env python3
"""Generate/check scoped custody V2 parity vectors with an integer account oracle."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core.asset_lane_custody_coordinator_v2 import (  # noqa: E402
    AssetLaneCustodyAcceptedV2,
    transition_asset_lane_custody_v2,
)
from src.core.asset_transfer_types_v2 import AssetTransferCommandV2  # noqa: E402
from src.core.global_settlement_types_v2 import canonical_global_bytes_v2  # noqa: E402
from tests.core.test_asset_lane_coordinator_v2 import (  # noqa: E402
    _context,
    _managed_command,
    _transfer_command,
)
from tests.core.test_asset_lane_custody_v2 import custody_state  # noqa: E402

FIXTURE = ROOT / "tests/data/asset_lane_custody_v2_golden.json"
SOURCES = (
    "tools/render_asset_lane_custody_v2_golden.py",
    "src/core/asset_lane_custody_state_v2.py",
    "src/core/asset_lane_custody_coordinator_v2.py",
    "src/core/asset_transfer_module_v2.py",
    "src/core/managed_asset_lifecycle_module_v2.py",
    "tests/core/test_asset_lane_custody_v2.py",
    "tests/core/test_asset_lane_coordinator_v2.py",
)


def _oracle(state, command, result):
    expected = {r.key: r.amount_atoms for r in state.transfer_state.balances}
    supplies = {r.asset: r.amount_atoms for r in state.transfer_state.supplies}
    if type(command) is AssetTransferCommandV2:
        policy = next(p for p in state.transfer_state.policies if p.asset == command.asset)
        changes = (
            (command.sender, -command.amount_atoms - policy.transfer_fee_atoms),
            (command.recipient, command.amount_atoms),
            (policy.fee_owner, policy.transfer_fee_atoms),
        )
    else:
        delta = (
            command.amount_atoms
            if command.command_kind == "managed_asset_issue"
            else -command.amount_atoms
        )
        changes = ((command.account_owner, delta),)
        supplies[command.asset] += delta
    for owner, delta in changes:
        key = (command.asset, owner, "accounts")
        expected[key] = expected.get(key, 0) + delta
    expected = {key: atoms for key, atoms in expected.items() if atoms}
    post = result.post_state
    if expected != {r.key: r.amount_atoms for r in post.transfer_state.balances}:
        raise ValueError("independent account oracle differs")
    if (
        supplies != {r.asset: r.amount_atoms for r in post.transfer_state.supplies}
        or post.custody != state.custody
    ):
        raise ValueError("independent supply or custody oracle differs")
    physical = sum(atoms for (asset, _, _), atoms in expected.items() if asset == command.asset)
    physical += sum(r.amount_atoms for r in state.custody if r.asset == command.asset)
    if result.effects.asset_conservation[0].owned_and_custodied_post_atoms != physical:
        raise ValueError("independent physical oracle differs")


def _case(name, state, command, expected="ACCEPTED", *, subject=None, nonce=1):
    context = _context(command, subject=subject, nonce=nonce)
    result = transition_asset_lane_custody_v2(context, state, command)
    if type(result) is AssetLaneCustodyAcceptedV2:
        if expected != "ACCEPTED":
            raise ValueError(f"{name}: required rejection accepted")
        _oracle(state, command, result)
        output = {
            "status": "ACCEPTED",
            "route": result.route,
            "source_leaf_journal_root": result.source_leaf_journal_root,
            "source_leaf_receipt_root": result.source_leaf_receipt_root,
            "post_state": result.post_state,
            "effects": result.effects,
            "module_journal": result.module_journal,
        }
    else:
        if result.code.value != expected:
            raise ValueError(f"{name}: expected {expected}, got {result.code.value}")
        output = {
            "status": "REJECTED",
            "route": result.route,
            "code": result.code,
            "pre_state_root": result.pre_state_root,
            "post_state_root": result.post_state_root,
            "effects": result.effects,
        }
    return {
        "name": name,
        "command_type": "TRANSFER"
        if type(command) is AssetTransferCommandV2
        else "MANAGED_LIFECYCLE",
        "context": context,
        "pre_state": state,
        "command": command,
        "output": output,
    }


def render() -> bytes:
    state = custody_state()
    transfer = _transfer_command(amount_atoms=10)
    cases = [
        _case("transfer_nonzero_custody", state, transfer),
        _case("transfer_zero_custody", custody_state(100, 0), transfer),
        _case("issue_nonzero_custody", state, _managed_command(amount_atoms=7)),
        _case(
            "burn_nonzero_custody",
            state,
            _managed_command(kind="managed_asset_burn", amount_atoms=7),
        ),
        _case(
            "burn_accounts_to_vault_only",
            state,
            _managed_command(kind="managed_asset_burn", amount_atoms=80),
        ),
        _case("issue_dormant_identity", custody_state(0, 0), _managed_command(amount_atoms=1)),
        _case(
            "burn_to_dormant",
            custody_state(1, 0),
            _managed_command(kind="managed_asset_burn", amount_atoms=1),
        ),
        _case("unauthorized", state, transfer, "UNAUTHORIZED_SUBJECT", subject="mallory"),
        _case("zero_transfer", state, _transfer_command(amount_atoms=0), "ZERO_AMOUNT"),
        _case(
            "insufficient_balance",
            state,
            _transfer_command(amount_atoms=79),
            "INSUFFICIENT_BALANCE",
        ),
    ]
    value = {
        "schema": "zenodex/asset-lane-custody-v2-golden/v1",
        "authority": "NONE",
        "source_sha256": {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in SOURCES},
        "nonclaim": "Listed-source bounded runtime parity; no signature, proof guest, publication or migration qualification.",
        "cases": cases,
    }
    canonical = canonical_global_bytes_v2(value)
    return (json.dumps(json.loads(canonical), indent=2, sort_keys=True) + "\n").encode()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    raw = render()
    if args.check:
        if not FIXTURE.exists() or FIXTURE.read_bytes() != raw:
            print("custody V2 golden vectors are missing or stale", file=sys.stderr)
            return 1
    else:
        FIXTURE.write_bytes(raw)
    print(
        "custody V2: 10 oracle-checked vectors match"
        if args.check
        else "custody V2: 10 oracle-checked vectors generated"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
