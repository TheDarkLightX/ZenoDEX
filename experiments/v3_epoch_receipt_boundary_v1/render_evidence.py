"""Declare the bounded root-epoch receipt execution boundary.

Replay: python3 -B -m experiments.v3_epoch_receipt_boundary_v1.render_evidence
Rendering only writes the declared hygiene packet. It executes no verifier,
test, publication, release activation, or production settlement action.
"""

import json

from experiments.v3_completion_followup_v1.render_evidence import ROOT, _render

BOUNDARY_TEST = "tests/integration/test_economic_epoch_verifier_boundary_v1.py"
TESTS = (
    "tests/core/test_global_settlement_abi_v1.py",
    "tests/core/test_asset_transfer_epoch_allocation_v1.py",
    "tests/core/test_asset_transfer_epoch_position_v1.py",
    "tests/integration/test_global_economic_durable_publisher_v1.py",
    "tests/integration/test_global_economic_epoch_journal_v1.py",
    "tests/integration/test_global_economic_publication_source_v1.py",
    "tests/integration/test_global_allocation_shadow_v1.py",
    BOUNDARY_TEST,
)
SOURCES = (
    "src/core/global_economic_proof_v1.py",
    "src/core/economic_initial_state_publisher_verification_v1.py",
    "src/integration/global_economic_epoch_verification_v1.py",
    "src/integration/economic_initial_state_publisher_verification_v1.py",
    "src/integration/global_economic_commit_v1.py",
    "src/integration/global_economic_durable_publisher_v1.py",
    "tests/core/lane_module_receipt_fixtures_v1.py",
    "tests/core/receipt_composition_fixtures_v1.py",
    "tests/core/test_asset_transfer_global_allocation_v1.py",
    "tests/core/test_asset_transfer_receipt_admission_v1.py",
    "tests/core/test_economic_receipt_verifier_release_v1.py",
    "tests/core/test_global_accounting_allocation_certificate_v1_golden.py",
    "tests/integration/publisher_receipt_port_fixtures_v1.py",
    "experiments/v3_epoch_receipt_boundary_v1/render_evidence.py",
    "docs/research/ZENODEX_RESOURCE_ARCHITECTURE_20260906.md",
    "docs/research/GLOBAL_SETTLEMENT_ABI_V1_REFERENCE_20260805.md",
)
EXECUTE_BEFORE_PREPARE_MUTANT = (
    BOUNDARY_TEST + "::test_execute_before_prepare_mutant_is_killed_by_the_no_call_law"
)


def main() -> None:
    _render(
        "epoch-receipt-boundary",
        SOURCES,
        TESTS,
        claim=(
            "The bounded root-epoch path prepares an immutable exact receipt subject "
            "in core, then the integration shell snapshots and executes its receipt, "
            "image and journal before minting a process-local publisher-bound witness. "
            "Genesis and migration retain a complete owned admission through their "
            "separate preparation/finish path. The declared corpus observes exact "
            "requests, retained publisher token and verifier-object identity, and "
            "bounded no-effect refusals."
        ),
        invariant="V3-EPOCH-RECEIPT-PREPARED-EXECUTION-BOUNDARY",
        families=["stateful", "differential", "mutation"],
        change_kind="behavior_change",
        created_date="2026-09-07",
        rejection_reason=(
            "Pure structural and prepared-subject refusals occur before the backend "
            "call. A backend exception leaves no registered epoch witness or publisher "
            "state change; commit admission retains exact publisher-token and verifier "
            "object identity checks. The generic shell continues to ignore the backend "
            "return value, while the separate measured Bound contract owns its exact "
            "None-success rule."
        ),
        bounds=[
            "The six pinned root-epoch/initial-state core and integration files retain the existing canonical journals, receipt digest, commit identity, state/effect refinements, numeric ceilings, and publisher bodies; no wire or economics field is added.",
            "PreparedEconomicEpochV1 is a consistency snapshot of fully admitted epoch facts and exact execution bytes; its shell copy rechecks those exact fields before I/O. It is distinct from initial-state preparation, which retains the complete owned admission and reruns complete admission validation while making its detached copy.",
            "The shell owns SuccinctReceiptVerifierV1, the private epoch witness token, lock and weak registry. Its publisher binding requires both the exact publisher token and the exact selected verifier object; raw prepared data supplies no publication authority.",
            "The eight pinned test files cover the former 305-test bounded regression set: pure preparation, exact three-field backend requests, initial genesis/migration execution, callback mutation, forged/subclass/field-injected subjects, publisher identity, backend exceptions, retry and durable controls.",
            "The core asset epoch composition boundary remains bounded to one through 64 inputs. The mounted isolated asset path and durable publisher retain their deliberately single-occurrence admission guard.",
            "The focused no-call mutation is declared narrative-only and executes inside the boundary test; it is not an external mechanical mutation result.",
        ],
        nonclaims=[
            "Rendering does not execute the declared tests, verifier, receipt, publication, release qualification, or production settlement path.",
            "Receipts, verifier replies, roots and publisher fixtures in this corpus are synthetic. No cryptographic validity, measured deployment, active-release, store-head, finality, or production authority follows.",
            "Private tokens, preparation markers, slots, and weak registries assume an intact interpreter, process, operating system, and publisher environment. They do not protect a compromised process.",
            "The generic shell retains its historical return-value behavior. This packet does not promote it to a measured verifier or manufacture a success-boolean authority path.",
            "The snapshot distinction between root-epoch field consistency and complete initial-state admission does not establish global completion, universal runtime refinement, a full FCIS closure, or a proof of all caller paths.",
            "BoundEconomicReceiptVerifierV1 deployment and unrelated tokenomics, fee, buyback, or callback owners remain separate obligations.",
            "No policy constant, canonical identity, historical evidence packet, native artifact, release image, or mounted one-occurrence policy changes through this renderer.",
        ],
    )
    path = ROOT / "tests/evidence/test_hygiene/THV1-20260907-epoch-receipt-boundary-v1.json"
    packet = json.loads(path.read_text())
    packet["mutations"] = [
        {
            "description": (
                "Narrative only: the focused boundary test executes the "
                "execute-before-prepare mutation and observes its forbidden backend "
                "call against the ordinary no-call law. The external evidence ledger "
                "must not count this as a mechanical mutation kill."
            ),
            "killed_by": EXECUTE_BEFORE_PREPARE_MUTANT,
            "narrative": True,
        }
    ]
    path.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="ascii")


if __name__ == "__main__":
    main()
