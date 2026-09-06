"""Render only this custody pipeline batch; preserve historical evidence.

Replay: python3 -B -m experiments.v3_custody_pipeline_v1.render_evidence
Rendering does not execute tests or promote release authority.
"""

from experiments.v3_completion_followup_v1.render_evidence import _render


def main() -> None:
    _render("custody-isolated-publication", (
        "experiments/v3_custody_pipeline_v1/render_evidence.py",
        "docs/research/ZENODEX_CUSTODY_PIPELINE_INTEGRATION_20260906.md",
        "src/integration/isolated_asset_receipt_pipeline_v1.py",
        "src/integration/global_economic_durable_publisher_v1.py",
        "src/integration/global_economic_epoch_journal_v1.py",
        "src/integration/isolated_profile_receipt_ports_v1.py",
        "src/core/asset_transfer_custody_semantics_v1.py",
        "src/core/asset_transfer_lane_module_custody_v1.py",
        "src/core/lane_module_release_route_binding_v1.py",
        "src/core/lane_module_receipt_verification_v1.py",
        "src/core/asset_transfer_epoch_allocation_v1.py",
        "src/core/asset_transfer_receipt_admission_v1.py",
        "src/core/global_accounting_lane_producers_v1.py",
        "tests/integration/custody_asset_receipt_pipeline_fixtures_v1.py",
    ), (
        "tests/integration/test_isolated_custody_asset_receipt_pipeline_v1.py",
        "tests/integration/test_global_economic_custody_pipeline_v1.py",
    ), claim="Fixed custody factories connect authenticated successor receipts to isolated store-derived allocation and atomic publication, preserving explicit predecessor claimant liabilities.",
       invariant="V3-CUSTODY-ISOLATED-PUBLICATION-CLAIMANT-COVERAGE",
       families=["stateful", "differential"], created_date="2026-09-06",
       rejection_reason="Receipt preparation supplies no writer. The actual publisher loads the predecessor and refuses uncovered custody before epoch verification, leaving logical state, replay, history and durable payload rows unchanged.",
       bounds=["seven pipeline cases and five publisher cases with the real sealed BLS executable explicitly supplied",
               "one occurrence, one asset-transfer lane",
               "explicit test-state custody and precommitted claimant liabilities",
               "exact receipt statements and unchanged source ownership",
               "invalid signature before receipt calls",
               "absent and mismatched claimant backing",
               "complete durable bundle and exact committed retry",
               "publisher allocation bypass and custody-to-legacy factory substitution mutants killed in disposable processes",
               "legacy zero-custody factory behavior retained"],
       nonclaims=["RISC0 process replies and release evidence are synthetic; successor test releases retain base guest image IDs, and no genuine guest or image qualification is established.",
                  "Sealed binary execution requires an explicitly configured checksum-qualified artifact; a skipped run supplies no such evidence.",
                  "Each signature factory retains its existing backend and trust premises.",
                  "Declared predecessor liabilities in test state do not approve production claimant or migration policy.",
                  "Existing publisher, allocation, epoch admission and journal sources remain unchanged.",
                  "No live profile activation, migration, production publication or whole-program completeness is established."])


if __name__ == "__main__":
    main()
