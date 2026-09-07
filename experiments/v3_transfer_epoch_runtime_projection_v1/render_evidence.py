"""Declare pure Python/Rust transfer-epoch proposal construction evidence.

Replay: python3 -B -m experiments.v3_transfer_epoch_runtime_projection_v1.render_evidence
Rendering records source pins and test obligations only. Python/Lean tests,
native Rust replay and fixture regeneration are separate executions.
"""

import json

from experiments.v3_completion_followup_v1.render_evidence import ROOT, _render
from experiments.v3_transfer_epoch_economic_tables_v1.render_evidence import (
    SOURCES as PREDECESSOR_SOURCES,
)
from tools.render_asset_transfer_epoch_projection_v1_golden import SOURCES as CORPUS_SOURCES

TESTS = (
    "tests/core/test_asset_transfer_epoch_projection_v1.py",
    "tests/core/test_asset_transfer_epoch_position_v1.py",
    "tests/core/test_asset_transfer_epoch_economic_tables_v1.py",
    "tests/formal/test_lean_asset_transfer_epoch_economic_tables_v1.py",
)
SOURCES = tuple(path for path in dict.fromkeys(
    PREDECESSOR_SOURCES + CORPUS_SOURCES + (
        "zk/global_settlement_abi_v1/src/lib.rs",
        "zk/global_settlement_abi_v1/src/state.rs",
        "zk/global_settlement_abi_v1/src/proof.rs",
        "zk/global_settlement_abi_v1/src/canonical.rs",
        "zk/global_settlement_abi_v1/src/asset_lane_projection.rs",
        "zk/global_settlement_abi_v1/src/asset_transfer_lane_module.rs",
        "zk/global_settlement_abi_v1/Cargo.toml",
        "zk/global_settlement_abi_v1/Cargo.lock",
        "zk/global_settlement_abi_v1/tests/asset_transfer_epoch_projection.rs",
        "zk/global_settlement_abi_v1/tests/asset_transfer_epoch_position.rs",
        "tests/data/asset_transfer_epoch_projection_v1_golden.json",
        "experiments/v3_transfer_epoch_runtime_projection_v1/render_evidence.py",
    )
) if path not in TESTS)


def main() -> None:
    _render(
        "transfer-epoch-runtime-projection",
        SOURCES,
        TESTS,
        created_date="2026-09-07",
        claim=(
            "Internal Python and Rust proposal constructors derive the shared-height asset "
            "epoch state from owned explicit inputs, preserving the full predecessor frame "
            "outside height, asset lane root, balances, supplies and canonical replay insertion. "
            "The updated formal fixture consumes actual Python runtime projections for both "
            "transfers under the unchanged 19 trace/table theorem signatures. A separate "
            "eleven-vector native corpus compares full states, canonical bytes, roots and "
            "subsequent allocation outcomes."
        ),
        invariant="V3-OWNED-ASSET-EPOCH-PROSPECTIVE-STATE",
        families=["formal", "differential", "stateful", "mutation"],
        rejection_reason=(
            "Invalid construction preserves all supplied inputs and creates no returned post "
            "state or external effect. Duplicate replay/occurrence identities and replay-table "
            "exhaustion are structural construction errors. Subsequent allocation rejection "
            "is a separate outcome; no public operation or mounted publication is modeled."
        ),
        bounds=[
            "Exact top-level Python input types precede detached snapshot reconstruction; direct construction cannot accept a supplied post_state. Rust returns cloned inputs behind read-only getters and does not implement Deserialize for proposal types.",
            "Two actual custody-complete transfers use one epoch height at source 7 and MAX_U64-1; the second module input consumes the first actual Python runtime projection. Existing standalone adjacent projection and exactly-one mount semantics remain unchanged.",
            "The full frame includes disabled lane roots, custody, liabilities, reserves, oracle occurrences, terminal obligations, history and outbox. The populated reserve/terminal/outbox vector intentionally fails later occurrence binding and grants no admission.",
            "Python boundary controls include duplicate replay ID, duplicate occurrence ID with distinct replay ID, 4095-to-4096 insertion, 4096-to-4097 structural rejection, and a MAX_U64 source whose ordinary proposal fails the existing epoch-height relation.",
            "The existing fresh 23-module Std-only Lean closure checks 19 unchanged theorem signatures and their standard axioms; finite runtime observations now consume the new Python constructor instead of the former test-only state builder.",
            "The generator first compares complete runtime endpoints against independently constructed legacy test endpoints. The Rust integration test separately consumes eleven records: four allocation successes and seven fixed source/index/context or unadmitted-frame outcomes.",
            "Native replay is separate from this packet's pytest runner: cargo test --offline --locked --manifest-path zk/global_settlement_abi_v1/Cargo.toml --test asset_transfer_epoch_projection --test asset_transfer_epoch_position. The corpus freshness command is python3 -B tools/render_asset_transfer_epoch_projection_v1_golden.py --check.",
            "The focused test's missing replay construction mutant reaches the ordinary GLOBAL_REPLAY_CONTINUITY_DRIFT checker. Prior plan-order, omission and i128-prefix controls are retained; these are in-test narrative mutation observations, not an external mechanical mutation score.",
        ],
        nonclaims=[
            "This constructor is ordinary internal proposal data. It confers no source authentication, receipt acceptance, aggregate Verified witness, finality, store, publication, release or settlement authority.",
            "The replay constructor exception boundary remains a conditional mounting blocker. A public caller must establish freshness/capacity preconditions or translate exact construction errors into typed operation rejection with end-to-end no-publication evidence before mounting.",
            "Schema-valid full-state construction is not sufficient for accounting, authorization, receipt or epoch admission. The complete-state relation and the remaining external authorities must still accept the exact output.",
            "The corpus and runtime observations are finite and source-specific. They are not universal Python/Rust/compiler refinement, exhaustive parser equivalence, a new theorem proving this constructor, or full formal-core completion.",
            "Mock receipt fixtures provide deterministic module outputs; no actual custody guest, cryptographic proof, full Mathlib build, deployment, multi-command publisher or production qualification is supplied.",
            "The constructor, test runner and local checkers assume intact language runtimes, processes and hosts. Snapshot ownership does not establish atomic store acquisition or protect a compromised operating system.",
            "No existing wire commitment, rounding policy, constant, guest image, historical packet, publisher implementation or exactly-one mount policy changes.",
        ],
    )
    path = ROOT / "tests/evidence/test_hygiene/THV1-20260907-transfer-epoch-runtime-projection-v1.json"
    packet = json.loads(path.read_text())
    packet["mutations"] = [{
        "description": (
            "Narrative only: omit replay insertion from the internal constructor and "
            "observe the unchanged allocation checker return GLOBAL_REPLAY_CONTINUITY_DRIFT. "
            "The external evidence ledger must not count this as a mechanical mutation kill."
        ),
        "killed_by": TESTS[0] + "::test_missing_replay_construction_mutant_is_rejected_by_existing_epoch_relation",
        "narrative": True,
    }]
    path.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="ascii")


if __name__ == "__main__":
    main()
