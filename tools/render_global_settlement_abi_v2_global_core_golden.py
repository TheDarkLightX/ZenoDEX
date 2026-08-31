#!/usr/bin/env python3
"""Render or check the research-only ABI V2 global-core parity vector.

The fixture binds deterministic Python values to Rust replay tests. It grants
no proof, runtime, settlement, migration, publisher, or production authority.
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

from src.core.global_economic_proof_v2 import EconomicCommandOccurrenceV2  # noqa: E402
from src.core.global_economic_state_effect_refinement_v2 import (  # noqa: E402
    GlobalEconomicStateEffectRefinementCandidateV2,
    refine_global_economic_state_effects_v2,
)
from src.core.global_economic_state_v2 import (  # noqa: E402
    GlobalEconomicStateV2,
    LaneStateRootV2,
    ReplayStateV2,
)
from src.core.global_settlement_types_v2 import (  # noqa: E402
    ALL_LANE_IDS_V2,
    ZERO_ROOT_V2,
    AssetConservationRowV2,
    AssetSupplyV2,
    EconomicAmountV2,
    EconomicEffectKindV2,
    EconomicEffectRowV2,
    GlobalEconomicEffectPlanV2,
    GlobalOracleOccurrencePlanV2,
    GlobalTerminalObligationPlanV2,
    LaneIdV2,
    LaneWriteV2,
    OracleOccurrenceDeltaV2,
    OracleOccurrenceStateV2,
    TerminalObligationDeltaV2,
    TerminalObligationStatusV2,
    TerminalObligationV2,
    canonical_global_bytes_v2,
)

FIXTURE_SCHEMA_V2: Final = "zenodex/global-settlement-abi-v2-global-core-golden/v1"
FIXTURE_PATH_V2: Final = Path(
    REPO_ROOT / "tests/data/global_settlement_abi_v2_global_core_golden.json"
)


def _root(value: int) -> str:
    if not 0 < value < 1 << 256:
        raise ValueError("fixture root ordinal is out of range")
    return f"0x{value:064x}"


def _vector(value: object, *, expected_root: str) -> dict[str, object]:
    canonical_bytes = canonical_global_bytes_v2(value)
    return {
        "canonical": json.loads(canonical_bytes),
        "canonical_bytes_sha256": hashlib.sha256(canonical_bytes).hexdigest(),
        "expected_root": expected_root,
    }


def _lane_roots() -> tuple[LaneStateRootV2, ...]:
    return tuple(
        LaneStateRootV2(
            lane_id=lane,
            module_release_id=_root(index + 1),
            enabled=lane is not LaneIdV2.EXTERNAL_CUSTODY,
            state_root=_root(index + 101),
        )
        for index, lane in enumerate(ALL_LANE_IDS_V2)
    )


def _replace_lane_roots(
    rows: tuple[LaneStateRootV2, ...],
    replacements: dict[LaneIdV2, str],
) -> tuple[LaneStateRootV2, ...]:
    return tuple(
        replace(row, state_root=replacements.get(row.lane_id, row.state_root))
        for row in rows
    )


def build_fixture_v2() -> dict[str, object]:
    pre_terminal = TerminalObligationV2(
        obligation_id="terminal-1",
        lane_id=LaneIdV2.SPOT_LIQUIDITY,
        claimant="alice",
        asset="USD",
        liability_domain="terminal-liability",
        amount_atoms=20,
        status=TerminalObligationStatusV2.OPEN,
    )
    post_terminal = replace(pre_terminal, amount_atoms=10)
    terminal_plan = GlobalTerminalObligationPlanV2(
        (TerminalObligationDeltaV2("terminal-1", pre_terminal, post_terminal),)
    )
    pre_oracle = OracleOccurrenceStateV2(
        oracle_id="oracle-1",
        occurrence_root=_root(301),
        observed_height=7,
        finalized=False,
    )
    post_oracle = replace(
        pre_oracle,
        occurrence_root=_root(302),
        observed_height=8,
        finalized=True,
    )
    oracle_plan = GlobalOracleOccurrencePlanV2(
        (OracleOccurrenceDeltaV2("oracle-1", pre_oracle, post_oracle),)
    )
    pre_lane_roots = _lane_roots()
    pre_state = GlobalEconomicStateV2(
        chain_id="zeno-v2-global-core-golden",
        deployment_root=_root(401),
        writer_epoch=4,
        height=7,
        profile_root=_root(402),
        lane_roots=pre_lane_roots,
        balances=(EconomicAmountV2("alice", "USD", "accounts", 100),),
        supplies=(AssetSupplyV2("USD", 200),),
        custody=(EconomicAmountV2("vault", "USD", "vault-custody", 50),),
        liabilities=(
            EconomicAmountV2("alice", "USD", "terminal-liability", 20),
        ),
        reserves=(
            EconomicAmountV2(
                "protocol:fee-unallocated-reserve",
                "USD",
                "zenoledger:protocol-fee-residue",
                50,
            ),
        ),
        oracle_occurrences=(pre_oracle,),
        replay_state=(),
        terminal_obligations=(pre_terminal,),
        history_root=ZERO_ROOT_V2,
        outbox=(),
    )
    occurrence = EconomicCommandOccurrenceV2(
        chain_id=pre_state.chain_id,
        deployment_root=pre_state.deployment_root,
        height=8,
        tx_index=2,
        op_index=1,
        command_kind="global_core_golden",
        command_body_hash=_root(403),
        route_release_id=_root(404),
        subject_id="alice",
        grant_root=_root(405),
        nonce=9,
        profile_root=pre_state.profile_root,
        pre_state_root=pre_state.state_root,
        consumed_object_ids=(),
    )
    post_lane_roots = _replace_lane_roots(
        pre_lane_roots,
        {
            LaneIdV2.ASSET_TRANSFER: _root(501),
            LaneIdV2.ORACLE_MARKET: _root(502),
            LaneIdV2.SPOT_LIQUIDITY: _root(503),
        },
    )
    post_state = GlobalEconomicStateV2(
        chain_id=pre_state.chain_id,
        deployment_root=pre_state.deployment_root,
        writer_epoch=pre_state.writer_epoch,
        height=8,
        profile_root=pre_state.profile_root,
        lane_roots=post_lane_roots,
        balances=(
            EconomicAmountV2("alice", "USD", "accounts", 90),
            EconomicAmountV2("bob", "USD", "accounts", 10),
        ),
        supplies=pre_state.supplies,
        custody=pre_state.custody,
        liabilities=(
            EconomicAmountV2("alice", "USD", "terminal-liability", 10),
        ),
        reserves=pre_state.reserves,
        oracle_occurrences=(post_oracle,),
        replay_state=(ReplayStateV2(occurrence.replay_id, occurrence.occurrence_id),),
        terminal_obligations=(post_terminal,),
        history_root=pre_state.history_root,
        outbox=(),
    )
    pre_by_lane = {row.lane_id: row for row in pre_lane_roots}
    post_by_lane = {row.lane_id: row for row in post_lane_roots}
    effect_plan = GlobalEconomicEffectPlanV2(
        rows=(
            EconomicEffectRowV2(
                EconomicEffectKindV2.ACCOUNT_MOVEMENT,
                "alice",
                "USD",
                "accounts",
                -10,
            ),
            EconomicEffectRowV2(
                EconomicEffectKindV2.ACCOUNT_MOVEMENT,
                "bob",
                "USD",
                "accounts",
                10,
            ),
            EconomicEffectRowV2(
                EconomicEffectKindV2.LIABILITY,
                "alice",
                "USD",
                "terminal-liability",
                -10,
            ),
        ),
        asset_conservation=(
            AssetConservationRowV2("USD", 200, 200, 200, 200, 0, 0),
        ),
        fee_conservation=(),
        lane_writes=tuple(
            LaneWriteV2(
                lane,
                pre_by_lane[lane].state_root,
                post_by_lane[lane].state_root,
            )
            for lane in sorted(
                (
                    LaneIdV2.ASSET_TRANSFER,
                    LaneIdV2.ORACLE_MARKET,
                    LaneIdV2.SPOT_LIQUIDITY,
                )
            )
        ),
        occurrence_consumptions=(occurrence.occurrence_id,),
        external_outbox_enqueue=(),
    )
    candidate = GlobalEconomicStateEffectRefinementCandidateV2(
        pre_state=pre_state,
        post_state=post_state,
        effect_plan=effect_plan,
        consumed_occurrences=(occurrence,),
        terminal_plan=terminal_plan,
        oracle_plan=oracle_plan,
    )
    witness = refine_global_economic_state_effects_v2(candidate)
    return {
        "fixture_schema": FIXTURE_SCHEMA_V2,
        "authority": witness.production_authority,
        "nonclaims": ["RISC0", "runtime", "publisher", "migration", "production"],
        "vectors": {
            "pre_state": _vector(pre_state, expected_root=pre_state.state_root),
            "post_state": _vector(post_state, expected_root=post_state.state_root),
            "effect_plan": _vector(
                effect_plan,
                expected_root=effect_plan.effect_plan_root,
            ),
            "occurrence": _vector(
                occurrence,
                expected_root=occurrence.occurrence_id,
            ),
            "terminal_plan": _vector(
                terminal_plan,
                expected_root=terminal_plan.plan_root,
            ),
            "oracle_plan": _vector(
                oracle_plan,
                expected_root=oracle_plan.plan_root,
            ),
        },
        "expected_replay_id": occurrence.replay_id,
        "expected_state_delta_root": witness.state_delta_root,
        "expected_refinement_root": witness.refinement_root,
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
        print(f"global ABI V2 global-core fixture written: {args.write}")
        return 0
    if args.check is None:
        sys.stdout.write(rendered)
        return 0
    try:
        observed = args.check.read_text(encoding="utf-8")
    except OSError as exc:
        print(f"global ABI V2 global-core fixture check failed: {exc}", file=sys.stderr)
        return 1
    if observed != rendered:
        print(f"global ABI V2 global-core fixture drift: {args.check}", file=sys.stderr)
        return 1
    print(f"global ABI V2 global-core fixture match: {args.check}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
