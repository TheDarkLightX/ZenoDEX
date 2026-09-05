#!/usr/bin/env python3
"""Replay: python3 tools/render_asset_transfer_global_allocation_v1_golden.py --check.

Omit --check to regenerate. These mock-receipt fixture inputs test only the pure
snapshot relation; Rust receipt admission is tested separately with opaque
witnesses from its recording verifier. No fixture grants authority.
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

from src.core.asset_transfer_global_allocation_v1 import (  # noqa: E402
    _global_allocation_binding_reject_v1,
)
from src.core.global_settlement_types_v1 import (  # noqa: E402
    EconomicAmountV1,
    canonical_global_bytes_v1,
)
from tests.core.test_asset_transfer_global_allocation_v1 import (  # noqa: E402
    _global_allocation_fixture,
)

FIXTURE = ROOT / "tests/data/asset_transfer_global_allocation_v1_golden.json"


def render() -> str:
    _, _, occurrence, accepted, _, predecessor, current = _global_allocation_fixture(
        controlled_atoms=100
    )
    foreign = "0x" + "99" * 32
    cases = [("exact", occurrence, predecessor, current, None)]
    for field, value in (
        ("chain_id", "foreign"),
        ("deployment_root", foreign),
        ("profile_root", foreign),
        ("writer_epoch", current.writer_epoch + 1),
    ):
        cases.append(
            (
                field,
                occurrence,
                predecessor,
                replace(current, **{field: value}),
                "GLOBAL_CONTEXT_DRIFT",
            )
        )
    cases.extend(
        [
            (
                "occurrence_subject",
                replace(occurrence, subject_id="mallory"),
                predecessor,
                current,
                "GLOBAL_OCCURRENCE_DRIFT",
            ),
            (
                "occurrence_body",
                replace(occurrence, command_body_hash=foreign),
                predecessor,
                current,
                "GLOBAL_OCCURRENCE_DRIFT",
            ),
            (
                "predecessor_claimant",
                occurrence,
                replace(
                    predecessor, liabilities=(replace(predecessor.liabilities[0], owner="mallory"),)
                ),
                current,
                "GLOBAL_OCCURRENCE_DRIFT",
            ),
            (
                "height",
                occurrence,
                predecessor,
                replace(current, height=2),
                "GLOBAL_OCCURRENCE_DRIFT",
            ),
            (
                "enabled",
                occurrence,
                predecessor,
                replace(
                    current,
                    lane_roots=(
                        current.lane_roots[0],
                        replace(current.lane_roots[1], enabled=True),
                        *current.lane_roots[2:],
                    ),
                ),
                "GLOBAL_LANE_SCOPE_UNSUPPORTED",
            ),
            (
                "root",
                occurrence,
                predecessor,
                replace(
                    current,
                    lane_roots=(
                        replace(current.lane_roots[0], state_root=foreign),
                        *current.lane_roots[1:],
                    ),
                ),
                "GLOBAL_LANE_ROOT_DRIFT",
            ),
            (
                "custodian",
                occurrence,
                predecessor,
                replace(current, custody=(replace(current.custody[0], owner="mallory"),)),
                "GLOBAL_PROJECTION_ROWS_DRIFT",
            ),
            (
                "claimant",
                occurrence,
                predecessor,
                replace(current, liabilities=(replace(current.liabilities[0], owner="mallory"),)),
                "GLOBAL_CLAIMANT_CONTINUITY_DRIFT",
            ),
            (
                "reserve",
                occurrence,
                predecessor,
                replace(current, reserves=(EconomicAmountV1("protocol", "USD", "reserve", 1),)),
                "GLOBAL_UNSUPPORTED_STATE",
            ),
            (
                "replay",
                occurrence,
                predecessor,
                replace(current, replay_state=()),
                "GLOBAL_REPLAY_CONTINUITY_DRIFT",
            ),
        ]
    )
    rows = []
    cases.append(
        (
            "balance",
            occurrence,
            predecessor,
            replace(
                current,
                balances=(
                    replace(current.balances[0], amount_atoms=current.balances[0].amount_atoms + 1),
                    *current.balances[1:],
                ),
            ),
            "GLOBAL_PROJECTION_ROWS_DRIFT",
        )
    )
    for name, command, pre, post, expected in cases:
        result = _global_allocation_binding_reject_v1(accepted, command, pre, post)
        actual = None if result is None else result.code.value
        if actual != expected:
            raise ValueError(f"independent expected outcome drift for {name}: {actual}")
        rows.append(
            {
                "name": name,
                "occurrence": command,
                "predecessor": pre,
                "current": post,
                "expected_code": expected,
            }
        )
    payload = json.loads(
        canonical_global_bytes_v1(
            {
                "accepted": {
                    "statement_root": accepted.statement_root,
                    "post_state": accepted.post_state,
                    "effects": accepted.effects,
                    "module_journal": accepted.module_journal,
                    "private_port": accepted.private_port,
                },
                "cases": tuple(rows),
            }
        )
    )
    payload["schema"] = "zenodex/asset-transfer-global-allocation-relation-golden/v1"
    payload["authority"] = "NONE"
    payload["source_sha256"] = {
        name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
        for name in (
            "src/core/asset_transfer_global_allocation_v1.py",
            "src/core/asset_transfer_receipt_admission_v1.py",
            "zk/global_settlement_abi_v1/src/asset_transfer_global_allocation.rs",
            "zk/global_settlement_abi_v1/src/asset_transfer_receipt_admission.rs",
        )
    }
    return json.dumps(payload, sort_keys=True, indent=2) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    content = render()
    if args.check:
        if FIXTURE.read_text() != content:
            raise SystemExit("global allocation binding fixture is stale")
    else:
        FIXTURE.write_text(content)


if __name__ == "__main__":
    main()
