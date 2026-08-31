#!/usr/bin/env python3
"""Render/check strict V2 wire-record golden bytes with authority NONE.

The fixture exercises the bounded Python wire DTOs only.  It provides no Rust,
proof, runtime, settlement, release, migration, publisher, or production
authority.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import replace
from pathlib import Path
from typing import Final

REPO_ROOT: Final = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.core.global_economic_refinement_outcome_v2 import (  # noqa: E402
    GlobalEconomicRefinementAcceptedV2,
    refine_global_economic_state_effects_outcome_v2,
)
from src.core.global_economic_state_effect_refinement_v2 import (  # noqa: E402
    GlobalEconomicStateEffectRefinementCandidateV2,
)
from src.core.global_economic_state_v2 import (  # noqa: E402
    GlobalEconomicStateV2,
    LaneStateRootV2,
)
from src.core.global_settlement_types_v2 import (  # noqa: E402
    ALL_LANE_IDS_V2,
    ZERO_ROOT_V2,
    ExternalOutboxEnqueueV2,
    GlobalEconomicEffectPlanV2,
    GlobalOracleOccurrencePlanV2,
    GlobalTerminalObligationPlanV2,
    LaneIdV2,
)
from src.core.global_settlement_wire_codec_v2 import (  # noqa: E402
    encode_global_settlement_wire_record_v2,
)
from src.core.global_settlement_wire_records_v2 import (  # noqa: E402
    WIRE_RECORD_TYPES_V2,
    wire_record_from_domain_v2,
)
from src.core.managed_asset_lifecycle_module_v2 import (  # noqa: E402
    transition_managed_asset_lifecycle_v2,
)
from tools import (  # noqa: E402
    render_global_settlement_abi_v2_asset_lane_coordinator_golden as lane_golden,
)
from tools import render_global_settlement_abi_v2_asset_origin_golden as origin_golden  # noqa: E402

FIXTURE_SCHEMA_V2: Final = "zenodex/global-settlement-abi-v2-wire-records-golden/v1"
FIXTURE_PATH_V2: Final = Path(
    REPO_ROOT / "tests/data/global_settlement_abi_v2_wire_records_golden.json"
)


def _root(value: int) -> str:
    if not 0 < value < 1 << 256:
        raise ValueError("fixture root ordinal is out of range")
    return f"0x{value:064x}"


def _global_state_v2() -> GlobalEconomicStateV2:
    return GlobalEconomicStateV2(
        chain_id="zeno-v2-wire-records",
        deployment_root=_root(1),
        writer_epoch=1,
        height=1,
        profile_root=_root(2),
        lane_roots=tuple(
            LaneStateRootV2(
                lane,
                _root(index + 10),
                lane is not LaneIdV2.EXTERNAL_CUSTODY,
                _root(index + 100),
            )
            for index, lane in enumerate(ALL_LANE_IDS_V2)
        ),
        history_root=ZERO_ROOT_V2,
    )


def _global_candidate_v2(
    effect_plan: GlobalEconomicEffectPlanV2 | None = None,
) -> GlobalEconomicStateEffectRefinementCandidateV2:
    state = _global_state_v2()
    return GlobalEconomicStateEffectRefinementCandidateV2(
        state,
        state,
        GlobalEconomicEffectPlanV2.empty() if effect_plan is None else effect_plan,
        (),
        GlobalTerminalObligationPlanV2.empty(),
        GlobalOracleOccurrencePlanV2.empty(),
    )


def build_wire_records_v2() -> tuple[object, ...]:
    """Build one valid value for each closed strict wire-record field set."""

    candidate = _global_candidate_v2()
    global_accepted = refine_global_economic_state_effects_outcome_v2(candidate)
    global_rejected = refine_global_economic_state_effects_outcome_v2(
        _global_candidate_v2(
            GlobalEconomicEffectPlanV2(
                (),
                (),
                (),
                (),
                (),
                (
                    ExternalOutboxEnqueueV2(
                        _root(3),
                        "external:adapter",
                        _root(4),
                        _root(5),
                    ),
                ),
            )
        )
    )
    if type(global_accepted) is not GlobalEconomicRefinementAcceptedV2:
        raise RuntimeError("wire fixture global acceptance unexpectedly rejected")

    managed_command = lane_golden._managed_command()
    managed_state = lane_golden._state().managed_leaf_state()
    managed_accepted = transition_managed_asset_lifecycle_v2(
        lane_golden._context(
            managed_command,
            subject_id="issuer",
            grant_root=lane_golden._root(5),
            nonce=2,
        ).managed_context(),
        managed_state,
        managed_command,
    )
    managed_rejected = transition_managed_asset_lifecycle_v2(
        lane_golden._context(
            managed_command,
            subject_id="issuer",
            grant_root=lane_golden._root(11),
            nonce=3,
        ).managed_context(),
        managed_state,
        managed_command,
    )

    origin_subject = origin_golden._build_subject_v2()
    origin_accepted = origin_subject.result
    origin_rejected = origin_golden.transition_asset_origin_registration_v2(
        replace(
            origin_subject.context,
            occurrence=replace(origin_subject.occurrence, subject_id="mallory"),
        ),
        origin_subject.pre_state,
        origin_subject.command,
    )

    transfer_command = lane_golden._transfer_command()
    asset_lane_context = lane_golden._context(
        transfer_command,
        subject_id="alice",
        grant_root=lane_golden._root(9),
        nonce=1,
    )
    asset_lane_accepted = lane_golden.transition_asset_lane_v2(
        asset_lane_context,
        lane_golden._state(),
        transfer_command,
    )
    asset_lane_rejected = lane_golden.transition_asset_lane_v2(
        lane_golden._context(
            transfer_command,
            subject_id="mallory",
            grant_root=lane_golden._root(9),
            nonce=3,
        ),
        lane_golden._state(),
        transfer_command,
    )
    values = (
        global_accepted,
        global_rejected,
        managed_accepted,
        managed_rejected,
        origin_accepted,
        origin_rejected,
        asset_lane_context,
        asset_lane_accepted,
        asset_lane_rejected,
        candidate,
        global_accepted.witness,
    )
    records = tuple(wire_record_from_domain_v2(value) for value in values)
    if tuple(type(record) for record in records) != WIRE_RECORD_TYPES_V2:
        raise RuntimeError("wire fixture does not cover the exact closed record registry")
    return records


def build_fixture_v2() -> dict[str, object]:
    records = build_wire_records_v2()
    rendered_records: dict[str, object] = {}
    for record in records:
        encoded = encode_global_settlement_wire_record_v2(record)
        rendered_records[type(record).__name__] = {
            "canonical": json.loads(encoded),
            "canonical_bytes_sha256": hashlib.sha256(encoded).hexdigest(),
        }
    return {
        "fixture_schema": FIXTURE_SCHEMA_V2,
        "authority": "NONE",
        "profile_authentication": "SHADOW",
        "records": rendered_records,
        "nonclaims": [
            "no Rust or Lean parity claim",
            "no proof, receipt, runtime, publisher, migration, or release authority",
            "no settlement or production authority",
            "the 1 MiB wire transport ceiling does not constrain GlobalEconomicStateV2 tables",
        ],
    }


def render_fixture_v2() -> str:
    return json.dumps(build_fixture_v2(), indent=2, sort_keys=True) + "\n"


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    output = parser.add_mutually_exclusive_group()
    output.add_argument("--check", type=Path, metavar="PATH")
    output.add_argument("--write", type=Path, metavar="PATH")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    rendered = render_fixture_v2()
    if args.write is not None:
        args.write.write_text(rendered, encoding="utf-8")
        print(f"global ABI V2 wire-record fixture written: {args.write}")
        return 0
    if args.check is None:
        sys.stdout.write(rendered)
        return 0
    try:
        observed = args.check.read_text(encoding="utf-8")
    except OSError as exc:
        print(f"global ABI V2 wire-record fixture check failed: {exc}", file=sys.stderr)
        return 1
    if observed != rendered:
        print(f"global ABI V2 wire-record fixture drift: {args.check}", file=sys.stderr)
        return 1
    print(f"global ABI V2 wire-record fixture match: {args.check}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
