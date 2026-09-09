#!/usr/bin/env python3
"""Retain exact custody/global disclosures and independently assembled statements."""

from __future__ import annotations

import argparse
import hashlib
import json
import struct
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core.asset_lane_state_v2 import AssetLaneContextV2  # noqa: E402
from src.core.global_settlement_types_v2 import canonical_global_bytes_v2  # noqa: E402
from tests.core.test_asset_lane_coordinator_v2 import (  # noqa: E402
    _managed_command,
    _transfer_command,
)
from tests.core.test_asset_lane_custody_global_v2 import global_case  # noqa: E402
from tests.core.test_asset_lane_custody_v2 import custody_state  # noqa: E402
from tools.render_asset_lane_custody_v2_golden import _oracle  # noqa: E402

FIXTURE = ROOT / "tests/data/asset_lane_custody_statement_v2_golden.json"
SOURCES = (
    "tools/render_asset_lane_custody_statement_v2_golden.py",
    "tools/render_asset_lane_custody_v2_golden.py",
    "tests/core/test_asset_lane_custody_global_v2.py",
    "tests/core/test_asset_lane_custody_v2.py",
    "tests/core/test_asset_lane_coordinator_v2.py",
    "src/core/asset_lane_custody_coordinator_v2.py",
    "src/core/asset_lane_custody_state_v2.py",
    "src/core/asset_transfer_module_v2.py",
    "src/core/managed_asset_lifecycle_module_v2.py",
)


def build_fixture() -> bytes:
    cases = []
    for name, accounts, vault, command in (
        ("transfer_with_claim", 80, 20, _transfer_command(amount_atoms=10)),
        ("issue_with_claim", 80, 20, _managed_command(amount_atoms=7)),
        (
            "burn_accounts_preserve_claim",
            80,
            20,
            _managed_command(kind="managed_asset_burn", amount_atoms=80),
        ),
        ("issue_dormant", 0, 0, _managed_command(amount_atoms=1)),
        ("burn_to_dormant", 1, 0, _managed_command(kind="managed_asset_burn", amount_atoms=1)),
    ):
        lane, accepted, before, after, occurrence = global_case(
            custody_state(accounts, vault), command
        )
        _oracle(lane, command, accepted)
        context = AssetLaneContextV2(
            before.writer_epoch,
            lane.transfer_state.module_release_id,
            before.state_root,
            occurrence,
        )
        # The expected payload is assembled without calling the new producer.
        # Its underlying economics have the separate integer row oracle above.
        statement = {
            "schema": "zenodex/asset-lane-custody-global-statement/v2",
            "module_journal": accepted.module_journal,
            "global_pre_state_root": before.state_root,
            "global_post_state_root": after.state_root,
        }
        # Independently encode the specified frame, without the new encoder.
        route_tag = 0 if accepted.route.value == "TRANSFER" else 1
        frame = b"ZDXCGV2\0" + bytes([route_tag])
        for value in (context, lane, command, before, after):
            raw = canonical_global_bytes_v2(value)
            frame += struct.pack("<I", len(raw)) + raw
        cases.append(
            {
                "name": name,
                "route": accepted.route,
                "context": context,
                "pre_state": lane,
                "command": command,
                "global_pre": before,
                "global_post": after,
                "statement": statement,
                "frame_sha256": hashlib.sha256(frame).hexdigest(),
            }
        )
    fixture = {
        "schema": "zenodex/asset-lane-custody-statement-golden/v2",
        "authority": "NONE",
        "nonclaim": "Five native economic payload vectors; no signed intent, measured guest, cryptographic receipt or publication qualification.",
        "source_sha256": {
            path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest() for path in SOURCES
        },
        "cases": cases,
    }
    return (
        json.dumps(
            json.loads(canonical_global_bytes_v2(fixture)), indent=2, sort_keys=True
        ).encode()
        + b"\n"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    expected = build_fixture()
    if args.check:
        if not FIXTURE.is_file() or FIXTURE.read_bytes() != expected:
            print(
                "custody statement V2: fixture differs; regenerate with this script",
                file=sys.stderr,
            )
            return 1
    else:
        FIXTURE.write_bytes(expected)
    print("custody statement V2: five oracle-checked disclosures match")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
