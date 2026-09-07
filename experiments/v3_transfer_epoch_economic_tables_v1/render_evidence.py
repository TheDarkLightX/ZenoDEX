"""Declare bounded input-trace economic-table evidence for transfer epochs.

Replay: python3 -B -m experiments.v3_transfer_epoch_economic_tables_v1.render_evidence
Rendering only writes the declared hygiene packet. It executes no Lean build,
runtime test, receipt, publication, release activation, or settlement action.
"""

import json

from experiments.v3_completion_followup_v1.render_evidence import ROOT, _render
from experiments.v3_transfer_epoch_state_closure_v1.render_evidence import (
    SOURCES as PREDECESSOR_SOURCES,
)

PROOF = "lean-mathlib/Proofs/AssetTransferEpochEconomicTablesV1.lean"
RUNTIME_TEST = "tests/core/test_asset_transfer_epoch_economic_tables_v1.py"
FORMAL_TEST = "tests/formal/test_lean_asset_transfer_epoch_economic_tables_v1.py"
TESTS = (RUNTIME_TEST, FORMAL_TEST)
SOURCES = tuple(
    dict.fromkeys(
        PREDECESSOR_SOURCES
        + (
            "lean-mathlib/Proofs/CheckedEconomicAggregationV1.lean",
            "lean-mathlib/Proofs/CheckedEpochEconomicTablesV1.lean",
            "lean-mathlib/Proofs/CanonicalEpochEconomicRowsV1.lean",
            "lean-mathlib/Proofs/GlobalSettlementCoreV2.lean",
            "lean-mathlib/Proofs/GlobalEconomicStateRefinementV2.lean",
            "src/core/epoch_effect_composition_v1.py",
            "src/core/global_economic_state_delta_v1.py",
            "src/core/global_settlement_types_v1.py",
            "tests/formal/test_lean_checked_epoch_economic_tables_v1.py",
            "tests/formal/test_lean_asset_transfer_global_successor_v1.py",
            "tests/formal/test_lean_asset_transfer_epoch_state_closure_v1.py",
            "experiments/v3_transfer_epoch_economic_tables_v1/render_evidence.py",
            "docs/research/ZENODEX_RESOURCE_ARCHITECTURE_20260906.md",
            "docs/research/GLOBAL_SETTLEMENT_ABI_V1_REFERENCE_20260805.md",
            "lean-mathlib/Proofs.lean",
            PROOF,
        )
    )
)
INPUT_PLAN_MUTANT = (
    FORMAL_TEST
    + "::test_input_plan_order_and_omission_mutants_change_observations_and_fail_theorems"
)
I128_MUTANT = (
    RUNTIME_TEST
    + "::test_actual_valid_leaves_kill_final_only_endpoint_mutant_at_i128_prefix"
)


def main() -> None:
    _render(
        "transfer-epoch-economic-tables",
        SOURCES,
        TESTS,
        claim=(
            "An input-indexed Std-only Lean relation retains the actual accepted custody "
            "inputs and their actual plans in command order. From the inherited shared-height "
            "continuation obligations it derives a bounded table chain, and characterizes the "
            "successful four-table checked fold by explicit PrefixFits. A successful i128 "
            "fold yields canonical endpoint rows. The declared Python and Lean tests compare bounded actual prospective "
            "transfer states/tables and retain ordered-history and signed-prefix controls."
        ),
        invariant="V3-CUSTODY-TRANSFER-EPOCH-INPUT-TABLE-CLOSURE",
        families=["formal", "differential", "stateful", "mutation"],
        change_kind="assurance_infrastructure",
        created_date="2026-09-07",
        rejection_reason=(
            "A failed checked fold yields no table output in the formal model. The bounded "
            "runtime controls reject reversed histories, malformed table rows, invalid arity, "
            "and an intermediate signed-i128 overflow while preserving their supplied inputs. "
            "No aggregate publication or receipt write is modeled."
        ),
        bounds=[
            "EpochInputTrace stores the actual List X.Input in Type and maps it definitionally to each actual result(input).plan and occurrence in original command order; it does not eliminate the Prop-valued EpochPrefix or choose plans existentially.",
            "The trace forgets one-way to the predecessor EpochPrefix, inheriting its count 0..64, explicit nonempty 1..64 corollary, carried StateInvariant, shared target height, replay fold, and actual-predecessor admission relation.",
            "The 19 explicit theorem signatures are consumed by the focused Lean test, whose fresh dependency closure compiles 23 Std-only modules when separately run. The permitted theorem axioms remain {propext, Classical.choice, Quot.sound}.",
            "TableChain comes from each actual shared-height economicTables obligation. The theorem states checked four-table endpoint equations and canonical emitted rows exactly under a successful checked fold, equivalently under explicit PrefixFits; PrefixFits is not silently derived from per-step admission or endpoint representability.",
            "The runtime test composes bounded actual custody-transfer plans, compares all four endpoint tables against an independent oracle at height 7 and the u64 maximum neighbour, and separately retains reverse-history, owner/domain/table, 0/65 arity, and intermediate signed-i128-prefix controls.",
            "Asset epoch composition remains bounded to one through 64 inputs. The mounted isolated asset pipeline and durable publisher retain their separate exactly-one admission policy.",
            "Reverse-plan, dropped-plan, and intermediate-i128-guard observations are narrative-only mutations executed inside the focused tests; they are not external mechanical mutation kills.",
        ],
        nonclaims=[
            "Rendering does not compile Lean, run the declared tests, execute a receipt, publish an epoch, activate a release, or grant settlement authority.",
            "The source StateInvariant and each input's EpochRequirements and accepted outcome are premises. The table chain and endpoint-key uniqueness are derived. PrefixFits remains an explicit condition for checked-fold success. None authenticates runtime input, roots, receipts, snapshots, authorization, or publication.",
            "The theorem does not establish global completion, an epoch-level Verified witness, aggregate atomic runtime folding, universal Python/Rust/compiler refinement, canonical byte encoding, storage-head safety, finality, or production qualification.",
            "The runtime prospective states and synthetic zero-fee overflow witness are bounded test evidence. They select no deployed policy and supply no cryptographic, measured-deployment, or production claim.",
            "The formal relation preserves command order while the Python composer normalizes its output rows and occurrence tuple for a different purpose; this packet does not claim those representations are universally refined.",
            "The renderer, focused test harness, and imported proof environment assume an intact interpreter, process, and host. They do not protect a compromised execution environment.",
            "No wire format, policy constant, release image, live authority, historical packet, or mounted exactly-one path changes through this renderer.",
        ],
    )
    path = ROOT / "tests/evidence/test_hygiene/THV1-20260907-transfer-epoch-economic-tables-v1.json"
    packet = json.loads(path.read_text())
    packet["mutations"] = [
        {
            "description": (
                "Narrative only: the focused Lean test observes the reversed actual "
                "input-plan order and localizes the resulting full-proof failure. The "
                "external evidence ledger must not count this as a mechanical kill."
            ),
            "killed_by": INPUT_PLAN_MUTANT,
            "narrative": True,
        },
        {
            "description": (
                "Narrative only: the focused Lean test observes the dropped first actual "
                "input plan and localizes the resulting full-proof failure. The external "
                "evidence ledger must not count this as a mechanical kill."
            ),
            "killed_by": INPUT_PLAN_MUTANT,
            "narrative": True,
        },
        {
            "description": (
                "Narrative only: the runtime test temporarily omits the intermediate "
                "signed-i128 guard and observes the forbidden cancellation-masked result. "
                "The external evidence ledger must not count this as a mechanical kill."
            ),
            "killed_by": I128_MUTANT,
            "narrative": True,
        },
    ]
    path.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="ascii")


if __name__ == "__main__":
    main()
