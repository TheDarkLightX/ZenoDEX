"""Declare bounded shared-height custody-transfer epoch-state evidence.

Replay: python3 -B -m experiments.v3_transfer_epoch_state_closure_v1.render_evidence
Rendering executes no proof or test and grants no economic or release authority.
"""

import json

from experiments.v3_completion_followup_v1.render_evidence import ROOT, _render
from experiments.v3_transfer_global_state_closure_v1.render_evidence import (
    SOURCES as PREDECESSOR_SOURCES,
)

PROOF = "lean-mathlib/Proofs/AssetTransferEpochStateClosureV1.lean"
TEST = "tests/formal/test_lean_asset_transfer_epoch_state_closure_v1.py"
SOURCES = tuple(dict.fromkeys(PREDECESSOR_SOURCES + (
    "src/core/asset_transfer_epoch_position_v1.py",
    "src/core/asset_transfer_global_allocation_v1.py",
    "src/core/asset_transfer_epoch_allocation_v1.py",
    "src/core/asset_transfer_receipt_admission_v1.py",
    "tests/formal/test_lean_asset_transfer_global_state_closure_v1.py",
    "experiments/v3_transfer_epoch_state_closure_v1/render_evidence.py",
    "docs/research/ZENODEX_RESOURCE_ARCHITECTURE_20260906.md",
    "lean-mathlib/Proofs.lean",
    PROOF,
)))


def main() -> None:
    _render(
        "transfer-epoch-state-closure", SOURCES, (TEST,),
        claim=(
            "A fresh Std-only Lean consumer closure with 27 theorem signatures "
            "establishes bounded shared-height state continuation for the restricted "
            "custody transfer: accepted attempts preserve the nine inherited state "
            "obligations and exact completed tables, rejected attempts are exact "
            "carried-state no-ops, index zero reuses the existing standalone Verified "
            "result, later positions use distinct SharedHeightVerified, and admitted "
            "prefixes are bounded at 0..64 with an explicit nonempty 1..64 corollary. "
            "Focused runtime observations compare the nonempty per-pair relation with "
            "actual custody/coordinator disclosures and separately exercise the legacy "
            "empty-custody aggregate checker."
        ),
        invariant="V3-CUSTODY-TRANSFER-EPOCH-SHARED-HEIGHT-CONTINUATION",
        families=["formal", "differential", "stateful", "mutation"],
        change_kind="assurance_infrastructure", created_date="2026-09-07",
        rejection_reason=(
            "The mathematical rejected continuation returns the exact carried state, "
            "empty effects and no occurrence. Runtime controls observe unchanged "
            "inputs and reject overflow, wrong shared-height and replay disclosures "
            "with the existing relation/checker codes; no epoch publication is modeled."
        ),
        bounds=[
            "Fresh Std-only Lean 4.27 closure consumes 27 public theorem signatures; all theorem axioms remain within {propext, Classical.choice, Quot.sound}; source registration is root-owned.",
            "EpochRequirements are input-only facts: source and position, index < 64, H+1 FitsU64, the appropriate predecessor height, H+1 occurrence, freshness, roots, command bounds and FeeEligible.",
            "An accepted custody-complete attempt derives the actual completed economic tables with four metadata changes, the shared target height, exact replay insertion and other-key frame, and nine inherited StateInvariant obligations.",
            "A rejected leaf returns the exact carried state, an empty effect plan and no occurrence.",
            "The first position equals the standalone successor and existing Verified; later positions use distinct SharedHeightVerified.",
            "EpochPrefix proves length 0..64, a static frame and context, the replay fold, and an explicit nonempty 1..64 shared-height corollary.",
            "Lane A uses the actual custody transition, public coordinator and epoch-position relation over a nonempty custody, backed-liability, replay and oracle witness at height 7 and the u64 maximum; the standalone projector's second shared-height refusal is retained.",
            "Lane B is a supplementary aggregate-checker control using the legacy composition fixture with a mock receipt verifier and empty custody; its scope is separate from Lane A.",
            "The actual checker rejects double-increment and replay-omission disclosures with exact codes and unchanged inputs.",
            "Two constructor mutant observations are narrative-only rows executed inside the focused test.",
        ],
        nonclaims=[
            "EpochRequirements and StateInvariant are premises, not runtime authentication or output assumptions.",
            "The restricted model has one enabled asset lane, empty reserves, an empty terminal registry and an empty outbox; it is not a complete lane lifecycle.",
            "Roots and identities are opaque; authenticity, hashing, canonical encoding and decoding remain external.",
            "Verified is established only at the first position; later positions deliberately use SharedHeightVerified, and no epoch-level Verified record is claimed.",
            "Lane A per-pair relation evidence and Lane B aggregate-checker evidence are distinct. Lane B uses the legacy empty-custody fixture and does not qualify nonempty custody.",
            "No aggregate authorization, atomic runtime fold, whole-epoch publication, certificate, receipt, snapshot authenticity, store-head, writer or publication/recovery authority is established.",
            "No CheckedEpochEconomicTablesV1 telescoping or universal Python/Rust/compiler refinement is established.",
            "The focused test's synthetic receipts and mock verifier grant no cryptographic, measured-deployment or production authority.",
            "The two controlled constructor observations execute inside the focused test; this packet claims no external mechanical mutation kill.",
            "No wire format, policy constant, release image, live authority or runtime production qualification changes.",
        ],
    )
    path = ROOT / "tests/evidence/test_hygiene/THV1-20260907-transfer-epoch-state-closure-v1.json"
    packet = json.loads(path.read_text())
    packet["mutations"] = [
        {
            "description": (
                "Narrative only: definitions-only good/bad observations and the "
                "localized full-proof failure for the height-double-increment "
                "constructor mutant are executed within the focused test; the "
                "external ledger must not count this as a mechanical kill."
            ),
            "killed_by": TEST + "::test_constructor_mutants_are_killed_by_the_shared_height_law",
            "narrative": True,
        },
        {
            "description": (
                "Narrative only: definitions-only good/bad observations and the "
                "localized full-proof failure for the replay-omission constructor "
                "mutant are executed within the focused test; the external ledger "
                "must not count this as a mechanical kill."
            ),
            "killed_by": TEST + "::test_constructor_mutants_are_killed_by_the_shared_height_law",
            "narrative": True,
        },
    ]
    path.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="ascii")


if __name__ == "__main__":
    main()
