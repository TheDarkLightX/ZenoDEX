"""Declare the restricted global transfer state-continuation proof subject.

Replay: python3 -B -m experiments.v3_transfer_global_state_closure_v1.render_evidence
Rendering executes no proof or test and grants no economic or release authority.
"""

import json

from experiments.v3_completion_followup_v1.render_evidence import ROOT, _render
from experiments.v3_transfer_global_successor_v1.render_evidence import (
    SOURCES as SUCCESSOR_SOURCES,
)

PROOF = "lean-mathlib/Proofs/AssetTransferGlobalStateClosureV1.lean"
TEST = "tests/formal/test_lean_asset_transfer_global_state_closure_v1.py"
SOURCES = tuple(dict.fromkeys(SUCCESSOR_SOURCES + (
    "experiments/v3_transfer_global_state_closure_v1/render_evidence.py",
    "docs/research/ZENODEX_RESOURCE_ARCHITECTURE_20260906.md",
    "tests/formal/test_lean_asset_transfer_global_successor_v1.py",
    PROOF,
)))


def main() -> None:
    _render(
        "transfer-global-state-closure", SOURCES, (TEST,),
        claim="The actual restricted custody-transfer global step preserves nine inherited state obligations for either leaf verdict; ten new input requirements then construct the next admission and its accepted global Verified witness.",
        invariant="V3-CUSTODY-TRANSFER-GLOBAL-STATE-CONTINUATION",
        families=["formal", "differential", "stateful", "mutation"],
        change_kind="assurance_infrastructure", created_date="2026-09-06",
        rejection_reason="The model's rejected continuation retains the exact carried state. The runtime leaf refuses zero amount with its exact rejection, unchanged owned input and empty effect plan; it does not publish a global transition.",
        bounds=[
            "Fresh Std-only Lean 4.27 dependency closure, nine independently consumed public theorem signatures, exact registration, literal selected source pins and permitted transitive axioms.",
            "Nine inherited state fields and ten next-input requirements are explicit; no desired output invariant or output table equality is a premise.",
            "Two actual Python custody transfers invoke the public coordinator and global projector with the first actual successor as the next predecessor.",
            "The nonempty fixture has two assets, ten custody atoms, six backed liability atoms, an existing oracle observation and prior replay state.",
            "The next Lean input carries continuedState from the first actual modeled result and derives its admission from the continuation theorem.",
            "Stale predecessor, reused replay key and reused occurrence identity refute the corresponding mathematical continuation requirements.",
            "An accepted transfer reaches maximum u64 height; the carried state cannot satisfy the next height-capacity requirement.",
            "A private constructor mutant carries leaf economics instead of global successor metadata; an executed bad observation and localized proof failure expose the defect.",
        ],
        nonclaims=[
            "The invariant is restricted to one enabled asset lane and empty reserves, terminal registry and outbox; it is not a complete lane lifecycle.",
            "Admission and continuation requirements are mathematical propositions, not executed runtime admission checks or automatic future-command authority.",
            "Supplied lane/global roots are opaque in Lean; source pins and finite runtime observations do not prove hashing, decoding, registry completeness or universal Python/Rust/compiler refinement.",
            "Model freshness refutations do not close the predecessor report's independent runtime occurrence-ID-guard coverage gap.",
            "State safety does not establish indefinite progress, generic runtime trace execution, authenticated snapshots, cryptographic receipt validity, writer authority or publication/recovery qualification.",
            "The accompanying architecture/Opus review is advisory and changes no runtime boundary; strict whole-system FCIS is not established.",
            "No runtime economics, wire formats, policy constants, release images, live authority or whole-program completion changes.",
        ],
    )
    path = ROOT / "tests/evidence/test_hygiene/THV1-20260906-transfer-global-state-closure-v1.json"
    packet = json.loads(path.read_text())
    packet["mutations"] = [{
        "description": "Tier 1: use leaf economic state in continuedState, losing actual global height and replay advancement; execute the bad observation and reject the complete proof at its continuation obligation.",
        "killed_by": TEST + "::test_continued_state_leaf_economic_mutant_is_observable_and_rejected",
        "mutant": {
            "path": PROOF,
            "needle_lines": ["  { (X.result input).post with economic := (X.step input).post }"],
            "replacement_lines": ["  { (X.result input).post with economic := (X.result input).post.economic }"],
        },
    }]
    path.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="ascii")


if __name__ == "__main__":
    main()
