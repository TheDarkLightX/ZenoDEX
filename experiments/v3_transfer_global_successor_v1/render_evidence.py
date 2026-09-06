"""Declare the constructive custody-transfer global successor proof subject.

Replay: python3 -B -m experiments.v3_transfer_global_successor_v1.render_evidence
Rendering executes no proof or test and grants no economic or release authority.
"""

import json

from experiments.v3_completion_followup_v1.render_evidence import ROOT, _render
from experiments.v3_transfer_custody_effect_plan_v1.render_evidence import (
    SOURCES as CUSTODY_SOURCES,
)

PROOF = "lean-mathlib/Proofs/AssetTransferGlobalSuccessorV1.lean"
TEST = "tests/formal/test_lean_asset_transfer_global_successor_v1.py"
SOURCES = tuple(dict.fromkeys(CUSTODY_SOURCES + (
    "experiments/v3_transfer_global_successor_v1/render_evidence.py",
    "docs/research/ZENODEX_TRANSFER_GLOBAL_SUCCESSOR_20260906.md",
    "tests/formal/test_lean_asset_transfer_custody_effect_plan_v1.py",
    "src/core/asset_lane_coordinator_v1.py",
    "src/core/global_economic_effect_projector_v1.py",
    "src/core/global_economic_proof_v1.py",
    PROOF,
)))


def main() -> None:
    _render(
        "transfer-global-successor", SOURCES, (TEST,),
        claim="An input-admitted accepted custody transfer constructs the existing nineteen-field global Verified witness from actual economic output, explicit commitments, one-step height advancement and exact replay insertion; leaf rejection is the exact global no-op.",
        invariant="V3-CONSTRUCTED-CUSTODY-TRANSFER-GLOBAL-SUCCESSOR",
        families=["formal", "differential", "mutation"],
        change_kind="assurance_infrastructure", created_date="2026-09-06",
        rejection_reason="The theorem returns the exact initial global state, empty plan and no occurrence for actual leaf rejection. Runtime refusals check exact classes/messages and unchanged canonical inputs; constructor failure is a separate outcome class.",
        bounds=[
            "Fresh Std-only Lean 4.27 source closure, thirty independently consumed public theorems plus acceptedWitness, exact import registration and permitted theorem axioms only.",
            "Eighteen input admission clauses and the unchanged nineteen-field Verified record; no desired output relation is a premise.",
            "Actual custody-complete economic output, one bounded height increment, one replay mapping and one enabled lane-root update construct the successor.",
            "One nonempty witness has two assets, custody 10, backed liability 6, a prior replay row and an existing oracle observation.",
            "Actual Python custody transition, public coordinator, global projector and restricted allocation checker are compared with the Lean construction under synthetic adjacent metadata.",
            "All modeled metadata and tables are observed, with finite present/absent registry queries and empty terminal/outbox lists; roots are explicit opaque inputs in Lean.",
            "Exact rejection, stale context, replay-key reuse, wrong height, wrong pre lane root, fee-owner-sender refusal and one malformed occurrence type preserve observed inputs.",
            "The u64 maximum height neighbor accepts; overflow constructors refuse and the model heightFits clause fails.",
            "Two source mutants execute bad metadata observations and fail within the exact replay theorem, excluding missing-identifier and syntax artifacts.",
        ],
        nonclaims=[
            "Admitted is a mathematical predicate; the raw modeled step does not execute admission and acceptedWitness requires proved input premises.",
            "Post lane and global roots are supplied opaque commitments, not computed or authenticated by Lean; no hashing or byte-encoding theorem is provided.",
            "The runtime occurrence-ID alias control reaches earlier context rejection; independent runtime occurrence-ID guard coverage remains open. The Lean dual-freshness control is model evidence only.",
            "The release, terminalEmpty and outboxEmpty premises retain runtime scope but are unused by the mathematical proof, which frames those fields.",
            "Finite comparisons do not establish universal Python/Rust/compiler refinement, complete registry or collection bounds, general terminal mapping, or full lane lifecycles.",
            "No cryptographic receipt, authenticated snapshot, current store head, writer authority, publisher/durability qualification, design optimality, production promotion or whole-program completion.",
            "No runtime economics, wire formats, policy constants, release images or live authority change.",
        ],
    )
    path = ROOT / "tests/evidence/test_hygiene/THV1-20260906-transfer-global-successor-v1.json"
    packet = json.loads(path.read_text())
    packet["mutations"] = [
        {
            "description": "Tier 1: omit the actual successor replay insertion; a definitions-only probe returns NONE and the full proof fails within successor_replay.",
            "killed_by": TEST + "::test_paired_constructor_mutants_are_killed_by_the_replay_relation",
            "mutant": {
                "path": PROOF,
                "needle_lines": ["    replayState := insertReplay (pre input).replayState input.occurrence }"],
                "replacement_lines": ["    replayState := (pre input).replayState }"],
            },
        },
        {
            "description": "Tier 1: omit the actual successor height increment; a definitions-only probe returns 7 and the full proof fails within successor_replay.",
            "killed_by": TEST + "::test_paired_constructor_mutants_are_killed_by_the_replay_relation",
            "mutant": {
                "path": PROOF,
                "needle_lines": ["    height := (pre input).height + 1"],
                "replacement_lines": ["    height := (pre input).height"],
            },
        },
    ]
    path.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="ascii")


if __name__ == "__main__":
    main()
