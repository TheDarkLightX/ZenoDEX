"""Render narrow source-pinned V3 evidence declarations without promoting claims.

Replay: python3 -B -m experiments.v3_completion_followup_v1.render_evidence
Tests and native build/qualification are separate executions, never inferred
from successful rendering. Historical packets remain unchanged.
"""

from __future__ import annotations

import ast
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
RENDERER = "experiments/v3_completion_followup_v1/render_evidence.py"


def _pin(path: str) -> dict[str, object]:
    return {"path": path, "sha256": hashlib.sha256((ROOT / path).read_bytes()).hexdigest()}


def _test_pin(path: str) -> dict[str, object]:
    nodes = [node.name for node in ast.parse((ROOT / path).read_bytes()).body
             if isinstance(node, ast.FunctionDef) and node.name.startswith("test_")]
    if not nodes:
        raise ValueError(f"no tests declared: {path}")
    return _pin(path) | {"node_ids": [f"{path}::{name}" for name in nodes]}


def _render(slug: str, sources: tuple[str, ...], tests: tuple[str, ...], *,
            claim: str, invariant: str, families: list[str], bounds: list[str],
            nonclaims: list[str], change_kind: str = "behavior_change",
            rejection_reason: str | None = None,
            created_date: str = "2026-09-05") -> None:
    evidence_id = "THV1-" + created_date.replace("-", "") + "-" + slug + "-v1"
    packet = {
        "schema": "zenodex/test-hygiene-evidence/v1", "evidence_id": evidence_id,
        "created_date": created_date, "change_kind": change_kind, "risk_class": "critical",
        "claim_scope": claim, "invariant_ids": [invariant],
        "failure_modes": bounds, "source_pins": [_pin(path) for path in sources + (RENDERER,)],
        "test_pins": [_test_pin(path) for path in tests], "removed_paths": [],
        "evidence_families": ["negative_regression", "boundary"] + families,
        "aaa": {"status": "applied", "reason": "Explicit fixture, one transition or observation, and independent exact output assertions."},
        "reject_is_noop": {"status": "applied", "reason": rejection_reason or "Precommit refusals preserve complete owned input or logical store snapshots; committed response loss explicitly has a different contract. The standalone BLS endpoint and transport have no economic write port."},
        "boundary_dimensions": [{"name": invariant, "points": bounds}],
        "mutations": [],
        "nonclaims": ["Packet rendering does not execute tests or establish completeness or production authority."] + nonclaims,
    }
    path = ROOT / "tests/evidence/test_hygiene" / (evidence_id + ".json")
    path.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="ascii")
    print(path.relative_to(ROOT))


def main() -> None:
    _render("publication-outcome-knowledge", (
        "src/integration/global_economic_durable_publisher_v1.py",
        "src/integration/global_economic_epoch_journal_v1.py",
    ), (
        "tests/integration/test_global_economic_publication_outcomes_v1.py",
        "tests/integration/test_global_economic_known_outcomes_v1.py",
        "tests/integration/test_global_economic_durable_publisher_v1.py",
    ), claim="Isolated publication distinguishes known PRE refusal, exact committed retry, response loss and unreadable durable history.",
       invariant="V3-PUBLICATION-OUTCOME-KNOWLEDGE", families=["stateful"],
       bounds=["before insert", "after insert before commit", "after commit before acknowledgment",
               "failed outcome projection", "known stale plus unreadable history",
               "distinct concurrent winner", "historical retry with newer lagging anchor"],
       nonclaims=["Synthetic RISC0 fixture replies are used; real BLS alone is not combined real-proof qualification.",
                  "Storage rollback, writer fencing, authority inode replacement, migrations and deployment closure remain outside this repair."])
    _render("reserved-lp-lock-replay", (
        "src/core/settlement_replay_remove_liquidity.py", "src/state/support_root.py",
        "src/core/batch_clearing_liquidity.py", "src/core/batch_clearing_apply.py",
        "src/core/batch_clearing_single_pool_liquidity.py",
        "zk/state_proof_risc0/shared/src/lib.rs",
    ), ("tests/core/test_settlement_replay_remove_liquidity_reserved_lock.py",
        "tests/core/test_batch_clearing_remove_liquidity_reserved_lock.py",
        "tests/integration/test_risc0_shared_fixture_equivalence.py"),
       claim="Legacy REMOVE_LIQUIDITY producer, apply, and replay paths refuse spending the reserved LP lock before mutation; the Rust shared transition carries the same guard and mirrored fixed vector.",
       invariant="SPOT-RESERVED-LP-LOCK-NONSPENDABLE", families=["stateful"],
       bounds=["zero amount rejection precedence", "one LP atom", "entire minimum locked share", "inactive pool", "ordinary holder withdrawal"],
       nonclaims=["No pool-close policy, terminal claimant, V3 lane mount or universal runtime/Rust refinement is established."])
    _render("checked-economic-aggregation", (
        "lean-mathlib/Proofs/CheckedEconomicAggregationV1.lean",
        "src/core/zdex_atomic_buyback_lane_coordinator_v2.py",
        "src/core/zdex_atomic_buyback_route_composition_v2.py",
    ), ("tests/formal/test_lean_checked_economic_aggregation_v1.py",),
       claim="Universal Lean checked-prefix arithmetic and all-key output theorem; finite differential correspondence to actual Python materializer/composer stages.",
       invariant="V3-CHECKED-COMPLETE-KEY-PREFIX-SUMS", families=["formal", "differential"],
       bounds=["i128 lower and upper neighbors", "intermediate overflow with representable final sum",
               "four complete key coordinates", "materialization before composition", "five executable model mutants"],
       nonclaims=["Finite helper comparisons do not prove universal Python/Rust/compiler refinement, canonical decoding or complete W09."])
    _render("sealed-command-bls", (
        "src/core/bls_command_verifier_protocol_v1.py",
        "src/integration/sealed_bls_command_verifier_v1.py",
        "src/integration/global_receipt_verifier_v1.py",
        "src/integration/economic_command_signature_verifier_deployment_v1.py",
        "zk/economic_command_bls_verifier_v1/Cargo.toml",
        "zk/economic_command_bls_verifier_v1/Cargo.lock",
        "zk/economic_command_bls_verifier_v1/src/main.rs",
        "zk/economic_command_bls_verifier_v1/tests/protocol.rs",
        "zk/economic_command_bls_verifier_v1/README.md",
    ), ("tests/integration/test_sealed_bls_command_verifier_v1.py",
        "tests/integration/test_sealed_bls_command_verifier_group_validation_v1.py"),
       claim="Standalone G2 Basic endpoint and immutable measured-byte Python transport implement a separate bounded request-digest-bound protocol.",
       invariant="V3-BLS-MEASURED-BYTES-EXECUTION", families=["differential"],
       bounds=["message length one and maximum neighbors", "public key and signature lengths",
               "foreign message key and ciphersuite", "infinity encoding", "digest and framing mismatch",
               "process failures", "sealed descriptor and acquired path replacement"],
       nonclaims=["The real transport test requires ZENODEX_BLS_VERIFIER_TEST_BINARY; a default skipped run supplies no real-execution evidence.",
                  "No release capability, active profile, publication mount or genuine five-receipt successor is created.",
                  "Python, the operating system, dynamic loader and native system libraries remain trusted."])
    _render("sealed-command-bls-deployment", (
        "src/core/bls_command_verifier_protocol_v1.py",
        "src/core/economic_command_signature_verifier_deployment_v1.py",
        "src/integration/sealed_bls_command_verifier_deployment_v1.py",
        "src/integration/sealed_bls_command_verifier_v1.py",
        "zk/global_settlement_abi_v1/src/economic_command_signature_verifier_deployment.rs",
        "zk/global_settlement_abi_v1/tests/bls_command_verifier_deployment.rs",
        "zk/global_settlement_abi_v1/tests/economic_command_signature_verifier_deployment.rs",
    ), ("tests/core/test_bls_command_verifier_deployment_v1.py",
        "tests/integration/test_sealed_bls_command_verifier_deployment_v1.py"),
       claim="Separate closed-protocol Python/Rust binders admit matching release, manifest, artifact and scope; the sealed shell executes the exact measured byte snapshot.",
       invariant="V3-BLS-RELEASE-EXECUTION-BINDING", families=["differential"],
       bounds=["legacy and successor protocol mismatches both directions", "key token98 and signature96 byte ceilings with neighbors",
               "artifact and manifest mismatch", "deployment and profile roots", "selection purpose",
               "legacy Rust SHADOW and VERIFY_ONLY refusal with stable active binding root",
               "real valid and invalid signatures"],
       nonclaims=["Release and evidence roots in the tests are synthetic; the tests do not issue or qualify a governed production release.",
                  "The Rust legacy binder now requires production admission, closing its previous purpose gap; compound-invalid first-error order differs by language.",
                  "No pipeline mount, active profile, publication authority or fresh genuine proof chain is added.",
                  "Changed shared ABI source requires selected guest remeasurement; historical guest receipts do not qualify new source."])
    _render("sealed-command-bls-pipeline", (
        "src/integration/isolated_asset_receipt_pipeline_v1.py",
        "src/integration/sealed_bls_command_verifier_deployment_v1.py",
        "src/integration/sealed_bls_command_verifier_v1.py",
        "src/integration/global_economic_durable_publisher_v1.py",
        "tests/integration/asset_receipt_pipeline_fixtures_v1.py",
        "tests/integration/publisher_receipt_port_fixtures_v1.py",
    ), ("tests/integration/test_global_economic_sealed_bls_pipeline_v1.py",
        "tests/integration/test_isolated_asset_receipt_pipeline_v1.py"),
       claim="A fixed sealed-BLS factory reauthenticates raw commands before isolated allocation admission and exact durable publication.",
       invariant="V3-SEALED-BLS-ISOLATED-PUBLICATION", families=["stateful"],
       bounds=["invalid signature before receipt calls with complete logical no-op",
               "valid signature and exact committed epoch bundle", "exact committed retry",
               "legacy protocol refusal before pipeline authority mint"],
       nonclaims=["The native executable must be supplied explicitly; skipped default execution is not qualification.",
                  "RISC0 replies and release coordinates are synthetic; this is isolated test-state integration evidence.",
                  "The existing zero-custody one-occurrence module remains selected; no new lane lifecycle, active profile or production release is qualified."])
    _render("checked-epoch-economic-tables", (
        "lean-mathlib/Proofs/CheckedEpochEconomicTablesV1.lean",
        "lean-mathlib/Proofs/CheckedEconomicAggregationV1.lean",
        "lean-mathlib/Proofs/GlobalSettlementCoreV2.lean",
        "lean-mathlib/Proofs/GlobalEconomicStateRefinementV2.lean",
        "lean-mathlib/Proofs.lean",
        "src/core/epoch_effect_composition_v1.py",
        "src/core/global_economic_state_delta_v1.py",
        "src/core/global_settlement_types_v1.py",
    ), ("tests/formal/test_lean_checked_epoch_economic_tables_v1.py",),
       claim="Universal Lean checked-prefix composition of four exact economic tables, under per-route table premises; finite correspondence to actual Python epoch composition and table checking.",
       invariant="V3-CHECKED-EPOCH-EXACT-TABLE-COMPOSITION", families=["formal", "differential"],
       change_kind="assurance_infrastructure",
       rejection_reason="Exact signed-overflow refusal and complete unchanged plan/state snapshots are observed at pure Python composition boundaries; the Lean model returns a typed error without an output accumulator.",
       bounds=["all four key coordinates and nine effect kinds", "balance custody liability and reserve tables",
               "26 actual composer histories and 129 ordered Lean command-prefix observations",
               "signed i128 upper and lower intermediate overflow despite a representable endpoint",
               "two locally exact runtime state histories with cancellation-masked overflow",
               "same-epoch command heights", "64-command positive control and 0/65 runtime arity refusals",
               "three temporary model mutants rejected by proof compilation"],
       nonclaims=["Per-route ExactEconomicTables is a theorem premise, not a proved property of every route verifier.",
                  "The arithmetic model has no command-count, metadata or whole-state admission guard; 0/65 controls expose this boundary.",
                  "The four-table positive example is not a conserved or authenticated global transition.",
                  "Canonical sorted unique zero-eliding tuples and universal Python/Rust/compiler correspondence remain unproved.",
                  "Mutation evidence is rejected proof compilation; no executed mutant runtime observation is claimed.",
                  "Supply conservation, authorization, complete lane lifecycles, receipts, publication and release qualification remain outside this theorem."])
    _render("writer-authority-identity", (
        "src/integration/global_economic_epoch_journal_v1.py",
        "src/integration/global_economic_durable_publisher_v1.py",
    ), ("tests/integration/test_global_economic_durable_publisher_v1.py",
        "tests/integration/test_global_economic_epoch_journal_v1.py",
        "tests/integration/test_global_economic_known_outcomes_v1.py",
        "tests/integration/test_global_economic_publication_outcomes_v1.py"),
       claim="A retained live authority identity detects observed pathname detachment and metadata drift before publication writes; postcommit observation failures remain indeterminate.",
       invariant="V3-LIVE-WRITER-AUTHORITY-IDENTITY", families=["stateful"],
       change_kind="bug_fix",
       rejection_reason="The precommit-only identity subtype is constructed before this attempt's first economic write; tests compare complete logical epoch-store snapshots. Postcommit controls retain the committed bundle and preserve indeterminate client knowledge.",
       bounds=["replacement before verification", "replacement during verification",
               "replacement during exact committed retry", "same-inode revocation and historical retry",
               "missing pathname and private-mode drift", "nonregular identity acquisition",
               "descriptor release and open failure", "postcommit outcome projection failure",
               "postcommit detachment before monotonic anchor advancement"],
       nonclaims=["The retained descriptor does not directly identify SQLite's internal attached descriptor.",
                  "Stable namespace around acquisition/ATTACH and between the final prewrite check and COMMIT remains a premise.",
                  "In-place restored bytes, epoch rollback or replacement, restart rollback and complete migration/writer fencing remain open.",
                  "The publisher process, operating system and filesystem remain trusted; receipt replies in these tests are synthetic."])
    _render("canonical-epoch-economic-rows", (
        "lean-mathlib/Proofs/CanonicalEpochEconomicRowsV1.lean",
        "lean-mathlib/Proofs/CheckedEpochEconomicTablesV1.lean",
        "lean-mathlib/Proofs/CheckedEconomicAggregationV1.lean",
        "lean-mathlib/Proofs/GlobalSettlementCoreV2.lean",
        "lean-mathlib/Proofs/GlobalEconomicStateRefinementV2.lean",
        "lean-mathlib/Proofs.lean",
        "src/core/epoch_effect_composition_v1.py",
        "src/core/global_economic_state_delta_v1.py",
        "src/core/global_settlement_types_v1.py",
    ), ("tests/formal/test_lean_canonical_epoch_economic_rows_v1.py",
        "tests/formal/test_lean_checked_epoch_economic_tables_v1.py"),
       claim="Constructive Lean canonical emission and checked endpoint-tuple equality for four economic tables under per-route table correctness and unique endpoint keys; finite full-tuple Python comparisons.",
       invariant="V3-CANONICAL-EPOCH-ECONOMIC-ROWS", families=["formal", "differential"],
       change_kind="assurance_infrastructure",
       rejection_reason="Checked signed-bound failures return no Lean delta tuple. Tests require exact Python builder/composer rejection and compare complete input snapshots for the composer histories. No publication or external effect is modeled.",
       bounds=["all nine kind tokens and four complete-key coordinates",
               "strict effect-key order and distinct table-delta order",
               "ASCII order boundaries", "cancellation and zero omission",
               "i128 lower and upper endpoint neighbors", "duplicate endpoint last-write versus sum behavior",
               "temporary executable model mutants"],
       nonclaims=["Endpoint amount-key uniqueness and per-route ExactEconomicTables are explicit premises.",
                  "Universal Python/Rust/compiler execution and canonical bytes remain unproved.",
                  "The list-based model makes no performance or complexity claim about Python dictionaries.",
                  "Token syntax, kind-specific sign admission, metadata, arity and resource limits remain separate obligations.",
                  "Supply conservation, authorization, lane lifecycles, receipts, publication and release qualification are outside this theorem."])
    _render("live-writer-store-pair", (
        "src/integration/global_economic_epoch_journal_v1.py",
        "src/integration/global_economic_durable_publisher_v1.py",
    ), ("tests/integration/test_global_economic_durable_publisher_v1.py",
        "tests/integration/test_global_economic_epoch_journal_v1.py",
        "tests/integration/test_global_economic_known_outcomes_v1.py",
        "tests/integration/test_global_economic_publication_outcomes_v1.py"),
       claim="The isolated verified writer retains and validates epoch and authority identities together; observed live detachment fails closed and postcommit uncertainty retains its outcome class.",
       invariant="V3-LIVE-WRITER-EPOCH-AUTHORITY-PAIR", families=["stateful"],
       change_kind="bug_fix", created_date="2026-09-06",
       rejection_reason="A narrow prewrite identity failure is issued before the attempt's first economic write; negative controls compare complete logical store contents. Postcommit failures preserve committed history and indeterminate client knowledge.",
       bounds=["valid live epoch replacement before proof", "epoch replacement during verification",
               "detached exact retry", "postcommit epoch replacement", "head and anchor observation",
               "paired descriptor close and partial acquisition failure", "nonblocking nonregular acquisition",
               "same-inode authority revocation and exact historical retry"],
       nonclaims=["The retained pair does not directly identify SQLite's internal main or attached descriptors.",
                  "Stable namespace during acquisition/open/attach and after the final identity observation remains a host premise.",
                  "Same-inode byte restoration, restart rollback, authenticated monotonic storage, migration and complete old-writer exclusion remain open.",
                  "Structural readers have no write capability. The publisher process, operating system and filesystem remain trusted; receipts in these tests are synthetic."])
    _render("sparse-transfer-accounting-trace", (
        "lean-mathlib/Proofs/AssetTransferSparseTablesV1.lean",
        "lean-mathlib/Proofs/AssetTransferSparseTraceV1.lean",
        "lean-mathlib/Proofs/AssetTransferRefinementV1.lean",
        "lean-mathlib/Proofs/AssetTransferCustodyCompletionV1.lean",
        "lean-mathlib/Proofs/AssetTransferCustodyCompositionV1.lean",
        "lean-mathlib/Proofs/CheckedSignedDeltaRefinementV1.lean",
        "lean-mathlib/Proofs/CheckedEconomicAggregationV1.lean",
        "lean-mathlib/Proofs/GlobalSettlementCoreV2.lean",
        "lean-mathlib/Proofs/GlobalEconomicStateRefinementV2.lean",
        "lean-mathlib/Proofs/CheckedEpochEconomicTablesV1.lean",
        "lean-mathlib/Proofs/CanonicalEpochEconomicRowsV1.lean",
        "lean-mathlib/Proofs.lean",
        "src/core/asset_transfer_module_v1.py",
        "src/core/asset_transfer_types_v1.py",
        "src/core/global_settlement_types_v1.py",
        "src/core/global_economic_state_delta_v1.py",
        "src/core/global_economic_state_effect_refinement_v1.py",
        "tests/formal/test_lean_checked_epoch_economic_tables_v1.py",
    ), ("tests/formal/test_lean_asset_transfer_sparse_tables_v1.py",
        "tests/formal/test_lean_asset_transfer_sparse_trace_v1.py"),
       claim="Constructed selected-policy sparse transfers derive exact economic tables and canonical post rows; constructed histories derive TableChain and checked endpoint accounting without assumed per-command table correctness. Runtime correspondence is finite.",
       invariant="V3-CONSTRUCTED-SPARSE-TRANSFER-ACCOUNTING-HISTORY",
       families=["formal", "differential", "stateful"],
       change_kind="assurance_infrastructure", created_date="2026-09-06",
       rejection_reason="The sparse step theorem returns the exact source state and empty projected plan on rejection. The history omits rejected attempts and continues from the same state. Python tests observe exact rejection codes, unchanged owned inputs, equal roots and empty effects.",
       bounds=["all complete amount-key coordinates and four physical or liability tables",
               "selected policy and unique positive accounts-domain source rows",
               "19 full leaf observations with three fee-owner alias classes",
               "u128 holding bounds and i128 effect bounds with neighbors",
               "4096-row replacement acceptance and growth refusal",
               "three six-attempt histories retaining two accepted plans",
               "actual checked aggregate acceptance and ordered prefix bounds",
               "six compiled and executed definitions-only semantic mutants",
               "41 sparse and five trace theorem transitive axiom audits"],
       nonclaims=["Policy selection, typed constructor admission, token syntax, canonical bytes and cryptographic hashes are separate boundaries.",
                  "Only accounting rows are projected; metadata, full conservation rows, receipt arity and publication are not modeled.",
                  "Equality with a supplied context subject is not authenticated command authority.",
                  "The positive sender-as-fee-owner leaf can fail the independent global fee-mirror guard; no economics are changed.",
                  "Universal Python/Rust/compiler refinement, whole-lane lifecycle completion and production qualification remain open.",
                  "The history fixes one selected policy and module release; no policy activation, migration or restart semantics are proved.",
                  "The list-based proof construction makes no runtime performance or complexity claim."])


if __name__ == "__main__":
    main()
