"""Render only the native custody route evidence; retain prior packets unchanged.

Replay: python3 -B -m experiments.v3_custody_native_route_v1.render_evidence
Rendering is separate from native execution and grants no authority.
"""

from experiments.v3_completion_followup_v1.render_evidence import _render


def main() -> None:
    _render("custody-native-route-preparation", (
        "experiments/v3_custody_native_route_v1/render_evidence.py",
        "zk/asset_transfer_custody_route_risc0/Cargo.toml",
        "zk/asset_transfer_custody_route_risc0/Cargo.lock",
        "zk/asset_transfer_custody_route_risc0/README.md",
        "zk/asset_transfer_custody_route_risc0/shared/Cargo.toml",
        "zk/asset_transfer_custody_route_risc0/shared/src/lib.rs",
        "zk/asset_transfer_custody_route_risc0/shared/tests/custody_route_preflight.rs",
        "zk/asset_transfer_custody_route_risc0/shared/tests/support/mod.rs",
        "zk/asset_transfer_custody_route_risc0/shared/tests/support/oversize.rs",
        "zk/asset_lane_custody_coordinator_risc0/shared/src/lib.rs",
        "zk/asset_transfer_custody_module_risc0/shared/src/lib.rs",
        "zk/global_settlement_abi_v1/src/asset_transfer_custody_semantics.rs",
        "zk/global_settlement_abi_v1/src/asset_transfer_global_allocation.rs",
        "zk/global_settlement_abi_v1/src/route_global_state_projection.rs",
        "zk/global_settlement_abi_v1/src/global_economic_state_effect_refinement.rs",
        "tests/data/asset_transfer_custody_release_binding_v1_golden.json",
    ), ("tests/integration/test_asset_transfer_custody_route_native_v1.py",),
       claim="Ordinary native custody-route preparation binds the governed semantic family, exact global allocation, projection and refinement, the outer canonical input ceiling, and all three selected release journal ceilings.",
       invariant="V3-CUSTODY-NATIVE-ROUTE-EXACT-STATE-AND-RESOURCE-BOUNDS",
       families=["differential"], created_date="2026-09-06",
       rejection_reason="Owned immutable inputs yield a prepared ordinary value or typed rejection; no receipt, economic writer, publication port or activation handle exists. Negative controls exercise typed, canonical and decoded entries.",
       bounds=["14 native tests replayed through installed Rust 1.90.0 and locked offline dependencies",
               "nonzero custody and exact independent component outputs; Python golden governance cross-check",
               "coherently rebuilt semantic-family mismatches and retained guard precedence",
               "global custody, account attribution, replay, occurrence and history drift",
               "selected module journal exact-limit success and one-byte-over refusal across all three entries",
               "valid 4096-row tables, exactly backed liabilities and 160-byte tokens",
               "9387855-byte route with 951101-byte module and 952015-byte lane inputs",
               "both missing guards reproduced as accepted counterexamples before repair",
               "zero/one/exact 8 MiB/8 MiB plus one byte decode boundaries and canonical spelling failures"],
       nonclaims=["The pytest gate invokes only the native shared target; unavailable toolchain/dependencies fail and never install or skip.",
                  "Bounded native evidence is not universal runtime/compiler refinement or proof execution.",
                  "Legacy composer source remains unchanged and retains its earlier typed-size and module-journal behavior.",
                  "Typed bounds canonicalize the caller-owned input; process memory exhaustion is not ruled out.",
                  "Images, cycle measurements, real receipts, pre-state authenticity, datastore continuity, release qualification and publication remain open."])


if __name__ == "__main__":
    main()
