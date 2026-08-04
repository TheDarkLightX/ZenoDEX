from __future__ import annotations

"""Bridge LLM scenario candidates into bounded stateful fuzz evidence.

This module is deliberately tooling-only. It does not authorize settlement and
it never upgrades bounded fuzz/concolic output above tested_discovery evidence.
"""

import json
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import Any, TypeAlias

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.stateful_feedback import DangerousSurface, load_dangerous_surface_manifest


SCENARIO_CANDIDATE_SCHEMA = "zenodex/stateful-scenario-candidate/v1"
SCENARIO_CANDIDATE_CHECK_SCHEMA = "zenodex/stateful-scenario-candidate-check/v1"
SHAPEFORGE_BRIDGE_SCHEMA = "zenodex/stateful-shapeforge-promotion-bridge/v1"
DISASTER_REACHABILITY_RATCHET_SCHEMA = "zenodex/stateful-disaster-reachability-ratchet/v1"
SCENARIO_RUN_RECEIPT_SCHEMA = "zenodex/stateful-scenario-run-receipt/v1"
PROOF_OBLIGATION_PACKET_SCHEMA = "zenodex/stateful-disaster-proof-obligation-packet/v1"
PROOF_OBLIGATION_CLOSURE_RECEIPT_SCHEMA = "zenodex/stateful-disaster-proof-obligation-closure-receipt/v1"
MINIMAL_WITNESS_LANGUAGE_AUDIT_SCHEMA = "zenodex/stateful-minimal-witness-language-audit/v1"
CROSS_SURFACE_WITNESS_EXPLORATION_SCHEMA = "zenodex/stateful-cross-surface-witness-exploration/v1"
DISASTER_SEARCH_EXPANSION_PLAN_SCHEMA = "zenodex/stateful-disaster-search-expansion-plan/v1"
DISASTER_SEARCH_EXPANSION_RECEIPT_SCHEMA = "zenodex/stateful-disaster-search-expansion-receipt/v1"
MAX_AGGREGATE_PYTEST_WORKERS = 4
_PytestShardKey: TypeAlias = tuple[str | None, str]
_ParsedPytestCommand: TypeAlias = tuple[list[str], tuple[_PytestShardKey, ...]]
_AxisPytestCommands: TypeAlias = tuple[dict[str, Any], list[_ParsedPytestCommand]]

DEFAULT_TARGET_MANIFEST = REPO_ROOT / "tools" / "acceptance_tcb_dangerous_surfaces.json"
DEFAULT_WORLD_MODEL = REPO_ROOT / "docs" / "zenodex" / "world_model_promoted" / "zenodex_world_model.seed.json"
DEFAULT_SHAPE_RATCHET = REPO_ROOT / "tools" / "check_shape_v1_ratchet.py"

EVIDENCE_ORDER = {
    "hypothesis": 0,
    "tested_discovery": 1,
    "implemented": 2,
    "contract": 3,
    "proved": 4,
}
MAX_SCENARIO_EVIDENCE = "tested_discovery"
SEVERITY_ORDER = {
    "unknown": -1,
    "low": 0,
    "medium": 1,
    "high": 2,
    "critical": 3,
}

FORMAL_LANE_KINDS = {"esso", "tau", "lean", "tla"}

SURFACE_FORMAL_LANES: dict[str, dict[str, Any]] = {
    "quote_receipt_certificate_boundary": {
        "obligation": "Route certificates remain bound to the quoted candidate set, quote body, winner index, and amount-out semantics.",
        "target_evidence_class": "contract_or_proved",
        "lanes": [
            {
                "kind": "esso",
                "name": "quote_receipt_certificate_gate_kernel",
                "artifacts": [
                    "src/kernels/dex/quote_receipt_certificate_gate_v1.yaml",
                    "tests/kernels/test_quote_receipt_certificate_gate_v1_native_adapter.py",
                ],
                "commands": [["pytest", "-q", "tests/kernels/test_quote_receipt_certificate_gate_v1_native_adapter.py"]],
            },
            {
                "kind": "lean",
                "name": "exact_in_route_certificate_binding",
                "artifacts": [
                    "lean-mathlib/Proofs/ZenoDEXExactInRouteCertificate.lean",
                    "tests/formal/test_lean_exact_in_route_certificate.py",
                ],
                "commands": [["pytest", "-q", "tests/formal/test_lean_exact_in_route_certificate.py"]],
            },
            {
                "kind": "fuzz_regression",
                "name": "route_certificate_sequence_witnesses",
                "artifacts": [
                    "tools/route_certificate_sequence_grammar_fuzz.py",
                    "tools/quote_receipt_cross_surface_sequence_grammar_fuzz.py",
                    "tests/integration/test_route_certificate_sequence_grammar_fuzz.py",
                    "tests/integration/test_quote_receipt_cross_surface_sequence_grammar_fuzz.py",
                ],
                "commands": [
                    ["pytest", "-q", "tests/integration/test_route_certificate_sequence_grammar_fuzz.py"],
                    ["pytest", "-q", "tests/integration/test_quote_receipt_cross_surface_sequence_grammar_fuzz.py"],
                ],
            },
        ],
    },
    "route_canonicalization_boundary": {
        "obligation": "Canonical route winner selection is stable under replay and candidate-set perturbation because the winner is the minimum under the declared total key.",
        "target_evidence_class": "proved",
        "lanes": [
            {
                "kind": "lean",
                "name": "route_rank_projection_and_certificate",
                "artifacts": [
                    "lean-mathlib/Proofs/ZenoDEXExactInRouteRankProjection.lean",
                    "lean-mathlib/Proofs/ZenoDEXExactInRouteCertificate.lean",
                    "tests/formal/test_lean_exact_in_route_rank_projection.py",
                    "tests/formal/test_lean_exact_in_route_certificate.py",
                ],
                "commands": [
                    ["pytest", "-q", "tests/formal/test_lean_exact_in_route_rank_projection.py"],
                    ["pytest", "-q", "tests/formal/test_lean_exact_in_route_certificate.py"],
                ],
            },
            {
                "kind": "esso",
                "name": "exact_in_route_rank_projection_packet",
                "artifacts": [
                    "src/kernels/dex/exact_in_route_rank_projection_packet_v1.yaml",
                    "tests/formal/test_esso_exact_in_route_rank_projection_packet.py",
                ],
                "commands": [["pytest", "-q", "tests/formal/test_esso_exact_in_route_rank_projection_packet.py"]],
            },
            {
                "kind": "fuzz_regression",
                "name": "route_canonicalization_sequence_witnesses",
                "artifacts": [
                    "tools/quote_receipt_route_canonicalization_sequence_grammar_fuzz.py",
                    "tests/integration/test_quote_receipt_route_canonicalization_sequence_grammar_fuzz.py",
                ],
                "commands": [["pytest", "-q", "tests/integration/test_quote_receipt_route_canonicalization_sequence_grammar_fuzz.py"]],
            },
        ],
    },
    "settlement_attestation_policy_boundary": {
        "obligation": "Settlement attestations fail closed on stale epochs, source allowlist drift, packet-hash mismatch, future timestamps, and signature tampering.",
        "target_evidence_class": "contract_or_proved",
        "lanes": [
            {
                "kind": "esso",
                "name": "settlement_spot_price_attestation_kernel",
                "artifacts": [
                    "src/kernels/dex/settlement_spot_price_attestation_v1.yaml",
                    "tests/formal/test_esso_settlement_spot_price_attestation.py",
                ],
                "commands": [["pytest", "-q", "tests/formal/test_esso_settlement_spot_price_attestation.py"]],
            },
            {
                "kind": "lean",
                "name": "settlement_price_history_certificate",
                "artifacts": [
                    "lean-mathlib/Proofs/ZenoDEXSettlementPriceHistoryCertificate.lean",
                    "tests/formal/test_lean_settlement_price_history_certificate.py",
                ],
                "commands": [["pytest", "-q", "tests/formal/test_lean_settlement_price_history_certificate.py"]],
            },
            {
                "kind": "fuzz_regression",
                "name": "settlement_attestation_sequence_witnesses",
                "artifacts": [
                    "tools/settlement_attestation_sequence_grammar_fuzz.py",
                    "tests/integration/test_settlement_attestation_sequence_grammar_fuzz.py",
                ],
                "commands": [["pytest", "-q", "tests/integration/test_settlement_attestation_sequence_grammar_fuzz.py"]],
            },
        ],
    },
    "stale_quote_receipt_boundary": {
        "obligation": "Quote receipts fail closed once a referenced pool snapshot drifts and cannot be repaired into a valid stale execution envelope.",
        "target_evidence_class": "contract_or_proved",
        "lanes": [
            {
                "kind": "esso",
                "name": "quote_receipt_pool_snapshot_gate",
                "artifacts": [
                    "src/kernels/dex/quote_receipt_pool_snapshot_gate_v1.yaml",
                    "tests/kernels/test_quote_receipt_pool_snapshot_gate_v1_native_adapter.py",
                ],
                "commands": [["pytest", "-q", "tests/kernels/test_quote_receipt_pool_snapshot_gate_v1_native_adapter.py"]],
            },
            {
                "kind": "tau",
                "name": "settlement_certificate_replay_compact_bundle",
                "artifacts": [
                    "src/tau_specs/recommended/settlement_v5_aligned_compact_bundle.tau",
                    "tests/tau/test_settlement_certificate_replay_compact_bundle.py",
                ],
                "commands": [["pytest", "-q", "tests/tau/test_settlement_certificate_replay_compact_bundle.py"]],
            },
            {
                "kind": "fuzz_regression",
                "name": "quote_receipt_staleness_sequences",
                "artifacts": [
                    "tools/quote_receipt_cross_surface_sequence_grammar_fuzz.py",
                    "tests/integration/test_quote_receipt_cross_surface_sequence_grammar_fuzz.py",
                    "tests/integration/test_dex_engine_quote_receipt_sequence_grammar_fuzz.py",
                ],
                "commands": [
                    ["pytest", "-q", "tests/integration/test_quote_receipt_cross_surface_sequence_grammar_fuzz.py"],
                    ["pytest", "-q", "tests/integration/test_dex_engine_quote_receipt_sequence_grammar_fuzz.py"],
                ],
            },
        ],
    },
    "stale_settlement_boundary": {
        "obligation": "Provided settlements fail closed after the execution surface changes and any applied settlement remains bound to current replayable witnesses.",
        "target_evidence_class": "contract_or_proved",
        "lanes": [
            {
                "kind": "esso",
                "name": "settlement_end_to_end_certificate_packet",
                "artifacts": [
                    "src/kernels/dex/settlement_end_to_end_certificate_packet_v1.yaml",
                    "tests/formal/test_esso_settlement_end_to_end_certificate_packet.py",
                ],
                "commands": [["pytest", "-q", "tests/formal/test_esso_settlement_end_to_end_certificate_packet.py"]],
            },
            {
                "kind": "lean",
                "name": "settlement_end_to_end_certificate_packet",
                "artifacts": [
                    "lean-mathlib/Proofs/ZenoDEXSettlementEndToEndCertificatePacket.lean",
                    "tests/formal/test_lean_settlement_end_to_end_certificate_packet.py",
                ],
                "commands": [["pytest", "-q", "tests/formal/test_lean_settlement_end_to_end_certificate_packet.py"]],
            },
            {
                "kind": "tau",
                "name": "settlement_proof_gate",
                "artifacts": [
                    "src/tau_specs/recommended/settlement_v1_proof_gate.tau",
                    "tests/tau/test_settlement_v1_proof_gate.py",
                ],
                "commands": [["pytest", "-q", "tests/tau/test_settlement_v1_proof_gate.py"]],
            },
            {
                "kind": "fuzz_regression",
                "name": "stale_settlement_sequence_witnesses",
                "artifacts": [
                    "tools/stale_settlement_sequence_grammar_fuzz.py",
                    "tests/integration/test_stale_settlement_sequence_grammar_fuzz.py",
                    "tests/integration/test_dex_engine_settlement_sequence_grammar_fuzz.py",
                ],
                "commands": [
                    ["pytest", "-q", "tests/integration/test_stale_settlement_sequence_grammar_fuzz.py"],
                    ["pytest", "-q", "tests/integration/test_dex_engine_settlement_sequence_grammar_fuzz.py"],
                ],
            },
        ],
    },
}

CRITICAL_DISASTER_SURFACE_IDS: tuple[str, ...] = (
    "quote_receipt_certificate_boundary",
    "route_canonicalization_boundary",
    "settlement_attestation_policy_boundary",
    "stale_quote_receipt_boundary",
    "stale_settlement_boundary",
)

CLOSED_DISASTER_SEARCH_AXIS_IDS: tuple[str, ...] = (
    "epoch_split_brain",
    "identity_registry_drift",
    "canonicalization_equivocation",
    "serialization_width_aliasing",
    "resource_budget_abort",
    "repair_after_tamper",
    "external_state_drift",
    "atomicity_partial_side_effect",
    "restart_replay_persistence",
    "dependency_outage_fail_closed",
    "reciprocal_netting_pair_forgery",
    "bounded_advisory_search_envelope",
    "exact_out_candidate_domain_explosion",
    "tau_gate_policy_aliasing",
    "confidential_receipt_attestation_drift",
    "batch_clearing_fragmentation_ordering",
    "perp_funding_liquidation_oracle_window",
    "proof_mining_packet_envelope_replay",
    "tau_net_client_transport_boundary",
    "settlement_proof_recompute_gate",
    "operations_parser_canonical_envelope",
    "dex_engine_sequence_anomaly_surface",
    "dex_core_ref_parity_drift",
    "boundary_concolic_wrapper_consistency",
    "exact_out_prefilter_winner_repair_boundary",
    "perp_engine_integration_oracle_bootstrap_boundary",
    "quote_receipt_transport_intent_boundary",
    "tau_runner_subprocess_transport_boundary",
    "dex_settlement_recovery_proof_unit_boundary",
)

SURFACE_WITNESS_LANGUAGE_REQUIREMENTS: dict[str, dict[str, Any]] = {
    "quote_receipt_certificate_boundary": {
        "language": "quote_certificate_binding_v1",
        "required_binding_fields": [
            "receipt_hash",
            "body_hash",
            "candidate_set_hash",
            "winner_index",
            "winner_quote_hash",
            "amount_out",
        ],
        "reject_ambiguity_tokens": [
            "candidate_set_hash mismatch",
            "winner_index mismatch",
            "candidate list mismatch",
        ],
    },
    "route_canonicalization_boundary": {
        "language": "route_total_key_certificate_v1",
        "required_binding_fields": [
            "candidate_set_hash",
            "winner_index",
            "winner_key",
            "tie_break_key",
            "canonical_route_hash",
        ],
        "reject_ambiguity_tokens": [
            "winner_quote mismatch",
            "candidate_set_hash mismatch",
            "winner_index mismatch",
        ],
    },
    "settlement_attestation_policy_boundary": {
        "language": "settlement_attestation_policy_witness_v1",
        "required_binding_fields": [
            "packet_hash",
            "signer_pubkey",
            "signed_at_epoch",
            "consumer_now_epoch",
            "source_id",
            "allowed_sources",
        ],
        "reject_ambiguity_tokens": [
            "settlement spot price attestation is stale",
            "source_id not allowlisted for signer",
            "packet_hash mismatch",
            "signature invalid",
        ],
    },
    "stale_quote_receipt_boundary": {
        "language": "quote_snapshot_freshness_witness_v1",
        "required_binding_fields": [
            "receipt_hash",
            "pool_id",
            "quote_pool_fingerprint",
            "current_pool_fingerprint",
            "quote_epoch",
        ],
        "reject_ambiguity_tokens": [
            "pool_snapshot_mismatch",
            "totals_mismatch",
        ],
    },
    "stale_settlement_boundary": {
        "language": "settlement_replay_freshness_witness_v1",
        "required_binding_fields": [
            "pre_state_commitment",
            "batch_commitment",
            "settlement_hash",
            "intent_ids",
            "nonce_snapshot",
            "pool_fingerprints",
        ],
        "reject_ambiguity_tokens": [
            "settlement mismatch",
            "missing settlement",
        ],
    },
}

CROSS_SURFACE_WITNESS_PAIRS: tuple[dict[str, Any], ...] = (
    {
        "pair_id": "quote_certificate_x_stale_quote_receipt",
        "surface_ids": ("quote_receipt_certificate_boundary", "stale_quote_receipt_boundary"),
        "bounds": {"max_depth": 3, "max_frontier": 32},
        "commands": [
            ["pytest", "-q", "tests/integration/test_quote_receipt_cross_surface_sequence_grammar_fuzz.py"],
            ["pytest", "-q", "tests/integration/test_dex_engine_quote_receipt_sequence_grammar_fuzz.py"],
        ],
    },
    {
        "pair_id": "settlement_attestation_x_stale_settlement",
        "surface_ids": ("settlement_attestation_policy_boundary", "stale_settlement_boundary"),
        "bounds": {"max_depth": 1, "max_frontier": 16},
        "commands": [
            ["pytest", "-q", "tests/integration/test_settlement_attestation_sequence_grammar_fuzz.py"],
            ["pytest", "-q", "tests/integration/test_stale_settlement_sequence_grammar_fuzz.py"],
        ],
    },
    {
        "pair_id": "route_canonicalization_x_quote_certificate",
        "surface_ids": ("route_canonicalization_boundary", "quote_receipt_certificate_boundary"),
        "bounds": {"max_depth": 4, "max_frontier": 48},
        "commands": [["pytest", "-q", "tests/integration/test_quote_receipt_route_canonicalization_sequence_grammar_fuzz.py"]],
    },
    {
        "pair_id": "stale_quote_receipt_x_stale_settlement",
        "surface_ids": ("stale_quote_receipt_boundary", "stale_settlement_boundary"),
        "bounds": {"max_depth": 2, "max_frontier": 32},
        "commands": [
            ["pytest", "-q", "tests/integration/test_dex_engine_quote_receipt_sequence_grammar_fuzz.py"],
            ["pytest", "-q", "tests/integration/test_stale_settlement_sequence_grammar_fuzz.py"],
        ],
    },
    {
        "pair_id": "route_canonicalization_x_stale_settlement",
        "surface_ids": ("route_canonicalization_boundary", "stale_settlement_boundary"),
        "bounds": {"max_depth": 4, "max_frontier": 48},
        "commands": [
            ["pytest", "-q", "tests/integration/test_quote_receipt_route_canonicalization_sequence_grammar_fuzz.py"],
            ["pytest", "-q", "tests/integration/test_stale_settlement_sequence_grammar_fuzz.py"],
        ],
    },
)

DISASTER_SEARCH_EXPANSION_AXES: tuple[dict[str, Any], ...] = (
    {
        "axis_id": "epoch_split_brain",
        "priority_score": 96,
        "surface_ids": (
            "settlement_attestation_policy_boundary",
            "stale_settlement_boundary",
            "stale_quote_receipt_boundary",
        ),
        "what_if": "A packet is individually fresh for one consumer but stale or future-dated for another consumer in the same replay chain.",
        "disaster_state_template": "epoch-local validity composes into cross-epoch settlement admission",
        "mutation_families": (
            "now_epoch-1/now_epoch/now_epoch+1 boundary sweeps",
            "valid attestation then delayed settlement replay",
            "future timestamp followed by state mutation and repair attempt",
        ),
        "bounded_harness_ideas": (
            "run attestation sequence and stale-settlement sequence as a paired frontier",
            "minimize witnesses that differ only by epoch boundary constants",
        ),
        "commands": (
            ("pytest", "-q", "tests/integration/test_settlement_attestation_sequence_grammar_fuzz.py"),
            ("pytest", "-q", "tests/integration/test_stale_settlement_sequence_grammar_fuzz.py"),
        ),
    },
    {
        "axis_id": "identity_registry_drift",
        "priority_score": 92,
        "surface_ids": (
            "settlement_attestation_policy_boundary",
            "operations_signature_reuse_boundary",
            "nonce_replay_guard",
        ),
        "what_if": "Signer, sender, source, or nonce identity changes after a witness is built but before it is replayed.",
        "disaster_state_template": "identity-local proof survives registry or sender-context drift",
        "mutation_families": (
            "same signature under changed sender context",
            "allowlist removal after attestation",
            "cross-batch nonce replay under equivalent-looking pubkeys",
        ),
        "bounded_harness_ideas": (
            "pair signature-reuse witnesses with nonce replay witnesses",
            "inject registry/source drift into attestation packet mutations",
        ),
        "commands": (
            ("pytest", "-q", "tests/integration/test_operations_signature_sequence_grammar_fuzz.py"),
            ("pytest", "-q", "tests/integration/test_nonce_replay_sequence_grammar_fuzz.py"),
            ("pytest", "-q", "tests/integration/test_settlement_attestation_sequence_grammar_fuzz.py"),
        ),
    },
    {
        "axis_id": "canonicalization_equivocation",
        "priority_score": 90,
        "surface_ids": (
            "route_canonicalization_boundary",
            "quote_receipt_certificate_boundary",
            "quote_receipt_pool_envelope_boundary",
        ),
        "what_if": "Two encodings name the same economic route but disagree about the candidate set, pool envelope, or tie-break witness.",
        "disaster_state_template": "equivalent route presentation bypasses canonical winner binding",
        "mutation_families": (
            "duplicate candidates with distinct hashes",
            "reordered equal-output ties",
            "pool fingerprint map with extra or missing unused pools",
        ),
        "bounded_harness_ideas": (
            "expand quote-receipt route-canonicalization frontier around equal-output ties",
            "compare candidate-set hash, winner index, and pool-envelope mutations in one sequence",
        ),
        "commands": (
            ("pytest", "-q", "tests/integration/test_quote_receipt_route_canonicalization_sequence_grammar_fuzz.py"),
            ("pytest", "-q", "tests/integration/test_route_certificate_sequence_grammar_fuzz.py"),
        ),
    },
    {
        "axis_id": "serialization_width_aliasing",
        "priority_score": 88,
        "surface_ids": (
            "api_request_authorization_boundary",
            "quote_receipt_certificate_boundary",
            "route_canonicalization_boundary",
        ),
        "what_if": "A value is full-width in one layer but truncated, normalized, or reinterpreted in another layer.",
        "disaster_state_template": "wide identifier or integer alias passes a narrow witness language",
        "mutation_families": (
            "leading-zero and max-width integer variants",
            "duplicate JSON keys and reordered canonical JSON",
            "low-bit-equal identifiers with full-width disagreement",
        ),
        "bounded_harness_ideas": (
            "add width-alias seeds to request-envelope and route-certificate boundary atlases",
            "promote every truncation-dependent survivor into a Tau/witness-language regression",
        ),
        "commands": (
            ("pytest", "-q", "tests/integration/test_api_server_request_grammar_fuzz.py"),
            ("pytest", "-q", "tests/integration/test_route_certificate_sequence_grammar_fuzz.py"),
            ("pytest", "-q", "tests/integration/test_tau_gate.py"),
        ),
    },
    {
        "axis_id": "resource_budget_abort",
        "priority_score": 82,
        "surface_ids": (
            "api_request_authorization_boundary",
            "route_canonicalization_boundary",
            "quote_receipt_certificate_boundary",
        ),
        "what_if": "A request is semantically rejected only after user-controlled search work has already consumed the per-request budget.",
        "disaster_state_template": "availability failure prevents guard completion",
        "mutation_families": (
            "max search parameter at cap and cap+1 BVA",
            "valid envelope with worst-case candidate explosion",
            "multi-option scans that combine individually bounded loops",
        ),
        "bounded_harness_ideas": (
            "treat timeout or budget exhaustion as a first-class disaster state",
            "keep API caps paired with exact-in, exact-out, and slippage regression tests",
        ),
        "commands": (
            ("pytest", "-q", "tests/integration/test_api_server_dex_api.py"),
            ("pytest", "-q", "tests/integration/test_api_server_request_grammar_fuzz.py"),
        ),
    },
    {
        "axis_id": "repair_after_tamper",
        "priority_score": 80,
        "surface_ids": (
            "quote_receipt_transport_boundary",
            "quote_receipt_certificate_boundary",
            "stale_quote_receipt_boundary",
            "stale_settlement_boundary",
        ),
        "what_if": "A mutated witness is repaired just enough to cross shallow hash checks while preserving deeper semantic drift.",
        "disaster_state_template": "rehash or rebuild converts tamper into admissible stale execution",
        "mutation_families": (
            "tamper then recompute outer hash only",
            "repair body hash but leave candidate-set hash stale",
            "rebuild settlement wrapper around stale inner witness",
        ),
        "bounded_harness_ideas": (
            "prioritize repair-after-tamper seeds over raw malformed seeds",
            "require minimizers to preserve the deepest reject token, not merely any reject",
        ),
        "commands": (
            ("pytest", "-q", "tests/integration/test_quote_receipt_cross_surface_sequence_grammar_fuzz.py"),
            ("pytest", "-q", "tests/integration/test_dex_engine_quote_receipt_sequence_grammar_fuzz.py"),
            ("pytest", "-q", "tests/integration/test_stale_settlement_sequence_grammar_fuzz.py"),
        ),
    },
    {
        "axis_id": "external_state_drift",
        "priority_score": 78,
        "surface_ids": (
            "settlement_attestation_policy_boundary",
            "stale_settlement_boundary",
            "stale_quote_receipt_boundary",
        ),
        "what_if": "Off-chain or chain-observed state drifts between witness construction and application without changing the witness bytes.",
        "disaster_state_template": "snapshot-valid witness survives live-state drift",
        "mutation_families": (
            "chain balance drift before claim or settlement",
            "oracle snapshot missing after clearing-price publication",
            "pool reserve mutation after quote receipt generation",
        ),
        "bounded_harness_ideas": (
            "make side-input drift explicit in the stateful action grammar",
            "check that drift syncs only where intended and rejects everywhere else",
        ),
        "commands": (
            ("pytest", "-q", "tests/integration/test_tau_testnet_dex_plugin.py"),
            ("pytest", "-q", "tests/core/test_perp_v2/test_engine.py"),
            ("pytest", "-q", "tests/integration/test_dex_engine_quote_receipt_sequence_grammar_fuzz.py"),
        ),
    },
    {
        "axis_id": "atomicity_partial_side_effect",
        "priority_score": 74,
        "surface_ids": (
            "stale_settlement_boundary",
            "nonce_replay_guard",
            "operations_signature_reuse_boundary",
        ),
        "what_if": "A multi-op transaction rejects after one subsystem has already computed or exposed a side effect.",
        "disaster_state_template": "failed transaction leaves replayable partial state or reward/accounting residue",
        "mutation_families": (
            "valid first op followed by malformed proof-mining or settlement op",
            "duplicate signature after an accepted warmup op",
            "proof context present but claim shape invalid",
        ),
        "bounded_harness_ideas": (
            "compare pre/post state roots for every rejected multi-op sequence",
            "add crash-or-exception as a minimized disaster outcome, not just logical acceptance",
        ),
        "commands": (
            ("pytest", "-q", "tests/integration/test_tau_testnet_dex_plugin.py"),
            ("pytest", "-q", "tests/integration/test_operations_signature_sequence_grammar_fuzz.py"),
            ("pytest", "-q", "tests/integration/test_nonce_replay_sequence_grammar_fuzz.py"),
        ),
    },
    {
        "axis_id": "restart_replay_persistence",
        "priority_score": 72,
        "surface_ids": (
            "stale_settlement_boundary",
            "stale_quote_receipt_boundary",
            "nonce_replay_guard",
        ),
        "what_if": "A snapshot, nonce journal, or state-root replay appears deterministic in isolation but changes meaning after process restart or import/export.",
        "disaster_state_template": "restart-stable bytes replay into a different semantic state",
        "mutation_families": (
            "snapshot export then import under reordered pools/accounts",
            "nonce replay across a restored state root",
            "quote or settlement witness generated before restart and applied after restart",
        ),
        "bounded_harness_ideas": (
            "pair snapshot determinism with nonce monotonicity and stale-witness checks",
            "treat state-root mismatch after semantic no-op replay as a disaster witness",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/integration/test_dex_snapshot.py",
                "tests/state/test_state_root_determinism.py",
                "tests/state/test_nonces.py",
            ),
        ),
    },
    {
        "axis_id": "dependency_outage_fail_closed",
        "priority_score": 70,
        "surface_ids": (
            "settlement_attestation_policy_boundary",
            "quote_receipt_certificate_boundary",
            "api_request_authorization_boundary",
        ),
        "what_if": "An external verifier, Tau state proof, or proof service is missing, stale, or malformed while the wrapper remains syntactically valid.",
        "disaster_state_template": "dependency outage degrades into optimistic proof acceptance",
        "mutation_families": (
            "missing proof verifier result with valid-looking envelope",
            "state_proof.present with mismatched committed state hash",
            "malformed verifier response that should be a hard reject rather than a skip",
        ),
        "bounded_harness_ideas": (
            "make unavailable dependencies first-class side inputs in proof-verifier fuzz",
            "keep Tau state-proof binding regressions in the same lane as verifier outage tests",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/integration/test_proof_verifier.py",
                "tests/integration/test_proof_verifier_fuzz.py",
                "tests/integration/test_tau_state_proof_binding.py",
            ),
        ),
    },
    {
        "axis_id": "numeric_boundary_coupling",
        "priority_score": 68,
        "surface_ids": (
            "route_canonicalization_boundary",
            "quote_receipt_certificate_boundary",
            "api_request_authorization_boundary",
        ),
        "what_if": "Two individually safe integer boundaries compose into overflow, zero-output, or impossible-route behavior at a higher layer.",
        "disaster_state_template": "boundary-valid arithmetic creates invalid advisory or certificate witness",
        "mutation_families": (
            "reserve max with swap amount max and reserve-growth edge",
            "u256 multiplication safety boundaries with exact-in/exact-out quote wrappers",
            "zero/one output transitions inside route and split certificates",
        ),
        "bounded_harness_ideas": (
            "combine domain-limit BVA with receipt/certificate validation, not arithmetic tests alone",
            "require advisory paths to return None instead of unverifiable route quotes outside the kernel domain",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/core/test_domain_bounds.py",
                "tests/core/test_cpmm_u256_safety.py",
                "tests/core/test_cpmm.py",
                "tests/core/test_exact_out_many_pool_bounded_oracle_v1.py",
            ),
        ),
    },
    {
        "axis_id": "advisory_cache_receipt_coherence",
        "priority_score": 66,
        "surface_ids": (
            "route_canonicalization_boundary",
            "quote_receipt_certificate_boundary",
            "quote_receipt_pool_envelope_boundary",
        ),
        "what_if": "A fast advisory cache returns a deterministic quote whose attached receipt or canonical-candidate witness cannot verify.",
        "disaster_state_template": "advisory fast path emits a route that automation cannot safely certify",
        "mutation_families": (
            "cached pool snapshot reused after route-relevant drift",
            "split route containing a zero-flow candidate member",
            "fast-route boundary amount that crosses kernel domain limits",
        ),
        "bounded_harness_ideas": (
            "treat every advisory quote as invalid unless its route receipt verifies against the same pool snapshot",
            "promote fast-path counterexamples into route-certificate candidate-set regressions",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/integration/test_fast_quote_router_v1.py",
                "tests/integration/test_api_server_http.py",
            ),
        ),
    },
    {
        "axis_id": "market_namespace_version_isolation",
        "priority_score": 64,
        "surface_ids": (
            "api_request_authorization_boundary",
            "operations_signature_reuse_boundary",
            "stale_settlement_boundary",
        ),
        "what_if": "A perps, clearinghouse, or alias/version namespace accepts an operation intended for a neighboring market surface.",
        "disaster_state_template": "namespace-valid action crosses into the wrong market or versioned reducer",
        "mutation_families": (
            "perps alias accepted under stale or wrong market type",
            "operator-only perps action with user-context sender fields",
            "malformed market/action parameters that should reject before reducer dispatch",
        ),
        "bounded_harness_ideas": (
            "run auth, parse, and alias guards as one namespace-isolation lane",
            "preserve syntactic action shape while flipping market id, alias, and operator fields",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/integration/test_perp_engine_auth_guards.py",
                "tests/integration/test_perp_engine_parse_guards.py",
                "tests/integration/test_perps_engine_alias.py",
            ),
        ),
    },
    {
        "axis_id": "reciprocal_netting_pair_forgery",
        "priority_score": 62,
        "surface_ids": (
            "stale_settlement_boundary",
            "settlement_attestation_policy_boundary",
            "route_canonicalization_boundary",
        ),
        "what_if": "A settlement fill is locally conservation-balanced but lacks the exact reciprocal COW counterparty that makes user-to-user netting admissible.",
        "disaster_state_template": "arbitrary direct netting masquerades as reciprocal COW settlement",
        "mutation_families": (
            "same-direction COW fills",
            "cross-pool reciprocal-looking fills",
            "duplicate or partial reciprocal fills with mismatched amount_in/amount_out",
        ),
        "bounded_harness_ideas": (
            "index filled COW pairs before replay and reject every unpaired survivor",
            "treat conservation-only acceptance as a disaster state even when balances sum to zero",
        ),
        "commands": (
            ("pytest", "-q", "tests/core/test_settlement_strong_validator.py", "-k", "cow"),
        ),
    },
    {
        "axis_id": "bounded_advisory_search_envelope",
        "priority_score": 60,
        "surface_ids": (
            "api_request_authorization_boundary",
            "quote_receipt_certificate_boundary",
            "route_canonicalization_boundary",
        ),
        "what_if": "A caller combines individually bounded quote, slippage, or exact-out knobs into a single request path that still performs unbounded work.",
        "disaster_state_template": "bounded-looking advisory endpoint admits CPU-exhaustion workload",
        "mutation_families": (
            "slippage option with victim_min_out <= 0 and large attacker cap",
            "exact-out max_iters/max_candidates/max_enumerated_candidates cap and cap+1",
            "adaptive dense search amount boundary with large reserve/fee gap",
        ),
        "bounded_harness_ideas": (
            "run API caps and slippage advisor BVA in one availability lane",
            "classify timeout as a failed search receipt rather than an inconclusive pass",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/core/test_slippage_advisor.py",
                "tests/integration/test_api_server_dex_api.py",
            ),
        ),
    },
    {
        "axis_id": "exact_out_candidate_domain_explosion",
        "priority_score": 58,
        "surface_ids": (
            "route_canonicalization_boundary",
            "quote_receipt_certificate_boundary",
            "api_request_authorization_boundary",
        ),
        "what_if": "Exact-out route certificates restrict each local field but still enumerate a candidate domain whose size or canonical winner relation escapes the declared bound.",
        "disaster_state_template": "exact-out selected domain exceeds bounded witness language",
        "mutation_families": (
            "candidate-count boundary and max_enumerated_candidates cap+1",
            "many-pool residual allocation with equal canonical keys",
            "quoted path presentation mismatch after candidate-domain repair",
        ),
        "bounded_harness_ideas": (
            "pair exact-out certificate fuzz with the canonical-domain bounded oracle",
            "promote every candidate-domain overflow into API cap regressions",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "-k",
                "not tau_steps_verify_when_tau_is_available",
                "tests/integration/test_exact_out_route_certificate.py",
                "tests/integration/test_exact_out_route_certificate_fuzz.py",
                "tests/core/test_exact_out_many_pool_canonical_domain_v1.py",
            ),
        ),
    },
    {
        "axis_id": "tau_gate_policy_aliasing",
        "priority_score": 56,
        "surface_ids": (
            "api_request_authorization_boundary",
            "settlement_attestation_policy_boundary",
            "route_canonicalization_boundary",
        ),
        "what_if": "A Tau policy witness passes under a neighboring profile, alias, or truncated binding language even though the intended runtime policy would reject.",
        "disaster_state_template": "policy-profile alias accepts a witness outside its semantic contract",
        "mutation_families": (
            "wrong Tau profile with shape-compatible inputs",
            "full-width identifier disagreement hidden by narrow witness fields",
            "ZUSD/Tau gate edge values crossing profile-specific semantics",
        ),
        "bounded_harness_ideas": (
            "pair Tau gate boundary tests with profile/alias metadata checks",
            "require every runtime-active Tau gate to declare its binding-width contract",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/integration/test_tau_gate.py",
                "tests/integration/test_tau_gate_boundary.py",
                "tests/integration/test_zusd_tau_gate.py",
            ),
        ),
    },
    {
        "axis_id": "zusd_oracle_recovery_split_brain",
        "priority_score": 54,
        "surface_ids": (
            "settlement_attestation_policy_boundary",
            "stale_settlement_boundary",
            "api_request_authorization_boundary",
        ),
        "what_if": "zUSD oracle recovery accepts a request whose committed oracle state, recovery-mode region, and redeem selector disagree about risk state.",
        "disaster_state_template": "oracle recovery region admits a risky zUSD state transition under split-brain oracle inputs",
        "mutation_families": (
            "oracle quorum boundary with one stale or missing commitment",
            "recovery mode risky-action request at region edge",
            "multi-redeem selector with stale MCR/oracle snapshot",
        ),
        "bounded_harness_ideas": (
            "pair oracle-recovery lifecycle tests with region partitions and MCR selector BVA",
            "treat recovery-mode admission under stale oracle commitment as a disaster state",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/integration/test_zusd_oracle_recovery_lifecycle.py",
                "tests/integration/test_zusd_recovery_mode_gate_regions.py",
                "tests/core/test_zusd_multi_oracle_commit_mcr.py",
                "tests/core/test_zusd_multi_redeem_selector.py",
            ),
        ),
    },
    {
        "axis_id": "confidential_receipt_attestation_drift",
        "priority_score": 52,
        "surface_ids": (
            "quote_receipt_transport_boundary",
            "api_request_authorization_boundary",
            "settlement_attestation_policy_boundary",
        ),
        "what_if": "A confidential request or attestation wrapper remains valid while the feature state, receipt body, or attestation evidence drifts underneath it.",
        "disaster_state_template": "confidential feature wrapper admits stale or unauthenticated plaintext/evidence",
        "mutation_families": (
            "receipt hash repaired around changed confidential body",
            "attestation edge values with stale feature status",
            "confidential admission request with mismatched verifier evidence",
        ),
        "bounded_harness_ideas": (
            "run confidential receipts and attestation edges as one transport/evidence lane",
            "promote any repaired wrapper that verifies after evidence drift into receipt regressions",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/core/test_confidential_extension_receipts.py",
                "tests/integration/test_confidential_attestation.py",
                "tests/integration/test_confidential_attestation_edges.py",
                "tests/integration/test_confidential_feature_status.py",
            ),
        ),
    },
    {
        "axis_id": "strategy_session_capability_replay",
        "priority_score": 50,
        "surface_ids": (
            "api_request_authorization_boundary",
            "operations_signature_reuse_boundary",
            "nonce_replay_guard",
        ),
        "what_if": "An autotrader strategy action is replayed across a session, wallet, or source-registry capability boundary that validates in isolation.",
        "disaster_state_template": "capability-local authorization composes into cross-session action admission",
        "mutation_families": (
            "session capability reused with different wallet capability",
            "signal source registry drift after observation packet construction",
            "strategy nonce replay under syntactically valid action bundle",
        ),
        "bounded_harness_ideas": (
            "join session, wallet, nonce, source-registry, and signal parsers into one replay lane",
            "reject any action whose capability proof is not bound to the current session and wallet context",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/core/test_strategy_session_capability_binding_guard_v1_adapter.py",
                "tests/core/test_strategy_wallet_capability_guard_v1_adapter.py",
                "tests/core/test_strategy_nonce_guard_v1_adapter.py",
                "tests/integration/test_autotrader_signal_registry.py",
                "tests/integration/test_autotrader_signals.py",
            ),
        ),
    },
    {
        "axis_id": "fire_registry_proof_tree_supply_chain",
        "priority_score": 48,
        "surface_ids": (
            "settlement_attestation_policy_boundary",
            "stale_settlement_boundary",
            "quote_receipt_certificate_boundary",
        ),
        "what_if": "A FIRE proof tree, registry snapshot, or settlement packet is individually well formed but belongs to a different registry epoch or package root.",
        "disaster_state_template": "proof-tree supply chain drift preserves a valid-looking settlement artifact",
        "mutation_families": (
            "registry snapshot changed after proof-tree certificate construction",
            "settlement packet root mismatch under repaired package metadata",
            "proof tree certificate with stale interface or rule registry",
        ),
        "bounded_harness_ideas": (
            "pair proof-tree certs with registry bundle and settlement packet checks",
            "treat registry epoch/root drift as a hard reject even when proof syntax validates",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/kernels/test_fire_proof_tree_cert_v1.py",
                "tests/kernels/test_fire_registry_bundle_v1.py",
                "tests/kernels/test_fire_settlement_packet_v1.py",
                "tests/integration/test_check_fire_registry_snapshot_cli.py",
            ),
        ),
    },
    {
        "axis_id": "batch_clearing_fragmentation_ordering",
        "priority_score": 46,
        "surface_ids": (
            "stale_settlement_boundary",
            "route_canonicalization_boundary",
            "quote_receipt_certificate_boundary",
        ),
        "what_if": "A batch settlement is value-conserving but uses a fragmented or noncanonical order that changes surplus, fill order, or witness language.",
        "disaster_state_template": "conservation-valid batch clears under noncanonical ordering or fragmented witness",
        "mutation_families": (
            "equal-volume equal-surplus tie with different order",
            "fragmented direct fills whose normal form differs from settlement replay",
            "candidate settlement stale after pool or balance snapshot mutation",
        ),
        "bounded_harness_ideas": (
            "pair batch clearing properties with normal-form and settlement witness tests",
            "require winner selection to remain min under the declared total key",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/core/test_batch_clearing.py",
                "tests/core/test_batch_clearing_properties.py",
                "tests/core/test_batch_clearing_global_refinement.py",
                "tests/core/test_batch_auction_settler_v1_witness.py",
                "tests/core/test_settlement_normal_form.py",
            ),
        ),
    },
    {
        "axis_id": "intent_auth_shape_replay",
        "priority_score": 44,
        "surface_ids": (
            "api_request_authorization_boundary",
            "operations_signature_reuse_boundary",
            "nonce_replay_guard",
        ),
        "what_if": "Intent authorization signs one normalized shape but runtime admission applies an equivalent-looking payload with different access or nonce semantics.",
        "disaster_state_template": "signed intent shape aliases into a different authorized action",
        "mutation_families": (
            "extra dead fields around signed intent auth shape",
            "nonce sender resolution drift between message and state",
            "access-control mutation after canonical intent id construction",
        ),
        "bounded_harness_ideas": (
            "compose intent auth message, shape gate, nonce, and access tests",
            "treat any signed-shape mismatch that reaches state mutation as a disaster witness",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/core/test_intent_access.py",
                "tests/core/test_dex_intent_auth_message.py",
                "tests/core/test_dex_intent_auth_shape_gate.py",
                "tests/kernels/test_dex_intent_auth_shape_gate_v1_native_adapter.py",
                "tests/state/test_intents.py",
            ),
        ),
    },
    {
        "axis_id": "perp_funding_liquidation_oracle_window",
        "priority_score": 42,
        "surface_ids": (
            "settlement_attestation_policy_boundary",
            "stale_settlement_boundary",
            "api_request_authorization_boundary",
        ),
        "what_if": "Perps funding or liquidation gates see an oracle snapshot as fresh while epoch settlement, auto-funding, or partial liquidation uses a neighboring stale window.",
        "disaster_state_template": "oracle-window disagreement admits funding or liquidation outside its intended epoch",
        "mutation_families": (
            "oracle_last_update at now-staleness-1/at/+1",
            "auto-funding after clearing price but before usable settlement oracle",
            "partial liquidation with stale or unauthorized risk envelope",
        ),
        "bounded_harness_ideas": (
            "run funding, auto-funding, liquidation eligibility, and integration partial-liquidation lanes together",
            "fail closed whenever oracle freshness predicates disagree across perps reducers",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/core/test_perp_funding_apply_gate.py",
                "tests/core/test_perp_apply_funding_auto_gate.py",
                "tests/core/test_perp_liquidation_eligibility_gate.py",
                "tests/integration/test_perp_engine_partial_liquidate.py",
            ),
        ),
    },
    {
        "axis_id": "proof_mining_packet_envelope_replay",
        "priority_score": 40,
        "surface_ids": (
            "api_request_authorization_boundary",
            "nonce_replay_guard",
            "operations_signature_reuse_boundary",
        ),
        "what_if": "A proof-mining packet has valid proof flags or claim identity locally but is replayed with a different packet envelope, nonce, or manager state.",
        "disaster_state_template": "proof-mining reward claim survives packet-envelope or identity drift",
        "mutation_families": (
            "proof_ok true with nonce_ok false or stale manager state",
            "slot identity drift after claimed slot registry mutation",
            "valid claim context wrapped in malformed manager packet envelope",
        ),
        "bounded_harness_ideas": (
            "join claim gate, identity gate, verification flags, packet envelope, and runtime context edges",
            "keep malformed claim handling as reject-without-side-effect rather than exception",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/core/test_proof_mining_claimability_gate.py",
                "tests/core/test_proof_mining_manager.py",
                "tests/integration/test_proof_mining_claimability.py",
                "tests/integration/test_proof_mining_runtime.py",
                "tests/integration/test_proof_mining_context_edges.py",
            ),
        ),
    },
    {
        "axis_id": "sealed_bid_reveal_commitment_binding",
        "priority_score": 38,
        "surface_ids": (
            "quote_receipt_transport_boundary",
            "nonce_replay_guard",
            "api_request_authorization_boundary",
        ),
        "what_if": "A sealed-bid or FHE plan receipt reveals under a different nonce, plaintext replay mode, or burn receipt than the original commitment.",
        "disaster_state_template": "commitment-valid sealed bid reveals into a different economic instruction",
        "mutation_families": (
            "commit receipt repaired around changed reveal nonce",
            "FHE trusted-plaintext replay result under bad oracle mode",
            "burn receipt hash mismatch after reveal-side metadata drift",
        ),
        "bounded_harness_ideas": (
            "pair sealed-bid, FHE alpha, and burn receipt hash checks",
            "reject every reveal whose commitment hash is not bound to the current nonce and payload",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/core/test_sealed_bid_auction.py",
                "tests/core/test_fhe_sealed_bid_alpha.py",
                "tests/core/test_burn_receipts.py",
                "tests/tau/test_burn_receipt_tau_traces.py",
            ),
        ),
    },
    {
        "axis_id": "curve_registry_dispatch_aliasing",
        "priority_score": 36,
        "surface_ids": (
            "route_canonicalization_boundary",
            "quote_receipt_certificate_boundary",
            "api_request_authorization_boundary",
        ),
        "what_if": "A route quote or receipt names a pool whose curve tag, params, or exact-out policy dispatches through a different curve implementation than the witness assumed.",
        "disaster_state_template": "curve-wrapper alias changes swap semantics under a valid route witness",
        "mutation_families": (
            "curve tag changed while reserves and pool id remain stable",
            "curve params malformed but wrapper path still produces quote",
            "exact-out policy edge differs between AMM dispatch and route certificate replay",
        ),
        "bounded_harness_ideas": (
            "combine curve selection, wrapper coverage edges, and AMM dispatch policy tests",
            "fail closed on any unsupported or mismatched curve tag before route receipt construction",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/core/test_curve_selection.py",
                "tests/core/test_curve_wrapper_coverage_edges.py",
                "tests/core/test_amm_dispatch_exact_out_policy.py",
                "tests/core/test_cubic_sum_amm.py",
                "tests/core/test_quartic_blend_amm.py",
                "tests/core/test_quintic_blend_amm.py",
            ),
        ),
    },
    {
        "axis_id": "vault_reward_carry_spendability",
        "priority_score": 34,
        "surface_ids": (
            "stale_settlement_boundary",
            "api_request_authorization_boundary",
            "nonce_replay_guard",
        ),
        "what_if": "Vault harvest or reward carry state is snapshot-valid but becomes spendable twice after restart, replay, or reward-deposit drift.",
        "disaster_state_template": "reward carry or harvest state creates duplicate spendable value",
        "mutation_families": (
            "harvest spendable guard at carry boundary",
            "reward deposit replay against restored vault state",
            "vault ref parity edge where carry remains after spend",
        ),
        "bounded_harness_ideas": (
            "pair vault ref parity with harvest spendable and reward carry native adapters",
            "treat duplicate spendable reward after replay as a state-root disaster",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/core/test_vault_ref_parity.py",
                "tests/kernels/test_vault_harvest_spendable_guard_v1_native_adapter.py",
                "tests/kernels/test_vault_reward_deposit_carry_v1_native_adapter.py",
            ),
        ),
    },
    {
        "axis_id": "tau_net_client_transport_boundary",
        "priority_score": 32,
        "surface_ids": (
            "api_request_authorization_boundary",
            "settlement_attestation_policy_boundary",
            "operations_signature_reuse_boundary",
        ),
        "what_if": "A Tau network client request, optional signature, or RPC response is syntactically valid but belongs to the wrong transport authority or signer context.",
        "disaster_state_template": "transport-valid TauNet message crosses signer or endpoint boundary",
        "mutation_families": (
            "optional signing mode with missing or mismatched key material",
            "TauNet response body accepted under wrong endpoint context",
            "client request replay with different transport/auth envelope",
        ),
        "bounded_harness_ideas": (
            "keep TauNet client tests separate from external Tau runner tests that skip without a binary",
            "treat skipped external-runner coverage as separate inconclusive work, not as unreachable",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/integration/test_tau_net_client.py",
                "tests/integration/test_tau_net_signing_optional.py",
            ),
        ),
    },
    {
        "axis_id": "tau_operator_policy_supply_chain",
        "priority_score": 30,
        "surface_ids": (
            "api_request_authorization_boundary",
            "operations_signature_reuse_boundary",
            "settlement_attestation_policy_boundary",
        ),
        "what_if": "A Tau operator policy artifact is signed, lowered, or deployed under one policy boundary but replayed under a neighboring evidence bundle or PCC obligation.",
        "disaster_state_template": "policy artifact supply-chain drift preserves deployable operator authority",
        "mutation_families": (
            "signed bundle with mismatched lowering receipt",
            "deployment contract whose evidence bundle root changed",
            "PCC obligation replayed across operator policy boundary metadata",
        ),
        "bounded_harness_ideas": (
            "compose boundary, deployment, evidence, lowering, PCC, and signed-bundle checks",
            "reject every policy artifact whose signed root is not bound to the current deployment contract",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/integration/test_tau_operator_policy_boundary.py",
                "tests/integration/test_tau_operator_policy_deployment_contract.py",
                "tests/integration/test_tau_operator_policy_evidence_bundle.py",
                "tests/integration/test_tau_operator_policy_lowering_receipt.py",
                "tests/integration/test_tau_operator_policy_pcc_obligation.py",
                "tests/integration/test_tau_operator_policy_signed_bundle.py",
            ),
        ),
    },
    {
        "axis_id": "settlement_proof_recompute_gate",
        "priority_score": 28,
        "surface_ids": (
            "stale_settlement_boundary",
            "settlement_attestation_policy_boundary",
            "quote_receipt_certificate_boundary",
        ),
        "what_if": "A settlement certificate, recompute proof, or runtime gate accepts a packet whose recomputed strong-settlement witness no longer matches.",
        "disaster_state_template": "proof-verifier wrapper accepts stale or weak settlement proof",
        "mutation_families": (
            "recompute batch proof result with stale settlement packet",
            "runtime certificate gate around mismatched strong validator output",
            "end-to-end settlement packet whose witness root differs from current state",
        ),
        "bounded_harness_ideas": (
            "pair recompute proof verifier with strong settlement certificate and runtime gate tests",
            "treat any validation path that bypasses strong settlement replay as a disaster state",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "-k",
                "not tau_bundle_steps_replay",
                "tests/integration/test_recompute_batch_proof_verifier.py",
                "tests/integration/test_validation_uses_strong_settlement_gate.py",
                "tests/integration/test_settlement_certificate_runtime_gate.py",
                "tests/integration/test_settlement_strong_certificate.py",
                "tests/integration/test_settlement_end_to_end_certificate_packet.py",
            ),
        ),
    },
    {
        "axis_id": "operations_parser_canonical_envelope",
        "priority_score": 26,
        "surface_ids": (
            "operations_signature_reuse_boundary",
            "api_request_authorization_boundary",
            "nonce_replay_guard",
        ),
        "what_if": "Operations parsing canonicalizes hex, signatures, or replay-protection envelopes differently than the operation executor consumes them.",
        "disaster_state_template": "parser-valid operation aliases into a different signed or replayable command",
        "mutation_families": (
            "hex casing, prefix, and width variants around signed operation fields",
            "grammar-valid operation with duplicate or dead signature fields",
            "replay-protection envelope with parser/executor sender mismatch",
        ),
        "bounded_harness_ideas": (
            "combine operations parsing/fuzz/grammar, hex parsing, intent signatures, and replay-protection tests",
            "treat parse-success plus executor-reject divergence as a boundary witness to minimize",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/integration/test_operations_parsing.py",
                "tests/integration/test_operations_fuzz.py",
                "tests/integration/test_operations_grammar_fuzz.py",
                "tests/integration/test_hex_parsing.py",
                "tests/integration/test_intent_signatures.py",
                "tests/integration/test_replay_protection.py",
            ),
        ),
    },
    {
        "axis_id": "resource_load_shedding_chaos_boundary",
        "priority_score": 24,
        "surface_ids": (
            "api_request_authorization_boundary",
            "settlement_attestation_policy_boundary",
            "quote_receipt_certificate_boundary",
        ),
        "what_if": "Load shedding, API chaos, or proof-verifier chaos turns a proof-gated request into an admitted-without-proof request.",
        "disaster_state_template": "availability fallback silently weakens authorization or proof requirement",
        "mutation_families": (
            "proof-gated region under shed-only path",
            "API chaos request that preserves auth envelope but drops proof evidence",
            "proof-verifier chaos response with fail-open admission",
        ),
        "bounded_harness_ideas": (
            "classify chaos exceptions as acceptable only when requests remain rejected or explicitly shed",
            "pair load-shedding regions with API and proof-verifier chaos tests",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/integration/test_resource_load_shedding_regret_guard_regions.py",
                "tests/chaos/test_api_server_chaos.py",
                "tests/chaos/test_proof_verifier_chaos.py",
            ),
        ),
    },
    {
        "axis_id": "cantor_region_partition_invariance",
        "priority_score": 22,
        "surface_ids": (
            "stale_settlement_boundary",
            "route_canonicalization_boundary",
            "api_request_authorization_boundary",
        ),
        "what_if": "A Cantor-region partition receipt is backend-invariant in one construction but verifies after the current region bundle, backend, or product receipts drift.",
        "disaster_state_template": "partition-valid assurance receipt hides backend or current-construction drift",
        "mutation_families": (
            "current construction mismatch after count or product receipt drift",
            "backend bundle hash mismatch under equal-payload flag",
            "region assurance report replayed with stale product receipts",
        ),
        "bounded_harness_ideas": (
            "pair region assurance bundle, verification, backend invariance, and report tests",
            "reject current-construction drift after lower-level hash consistency checks pass",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/integration/test_cantor_region_assurance_bundle.py",
                "tests/integration/test_cantor_region_assurance_verify.py",
                "tests/integration/test_cantor_region_backend_invariance_receipt.py",
                "tests/integration/test_cantor_region_backend_invariance_verify.py",
                "tests/integration/test_cantor_region_report.py",
            ),
        ),
    },
    {
        "axis_id": "autotrader_policy_artifact_replay",
        "priority_score": 20,
        "surface_ids": (
            "api_request_authorization_boundary",
            "operations_signature_reuse_boundary",
            "settlement_attestation_policy_boundary",
        ),
        "what_if": "An autotrader decision, stage certificate, live release certificate, or signed policy bundle is replayed after the policy surface changed.",
        "disaster_state_template": "policy-valid automated trading artifact executes under stale policy or decision context",
        "mutation_families": (
            "decision witness reused under changed client policy bundle",
            "stage certificate mismatched with live release certificate",
            "signed policy verification after policy text or surface drift",
        ),
        "bounded_harness_ideas": (
            "compose decision, stage, release, signed-policy, and client policy surface tests",
            "treat policy artifact replay as rejected unless every root binds to the current policy surface",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/integration/test_autotrader_decision.py",
                "tests/integration/test_autotrader_stage_certificate.py",
                "tests/integration/test_autotrader_live_release_certificate.py",
                "tests/integration/test_autotrader_policy_sign_verify_cli.py",
                "tests/agents/test_autotrader_client_policy_bundle.py",
                "tests/agents/test_autotrader_client_policy_surface.py",
            ),
        ),
    },
    {
        "axis_id": "state_accounting_size_boundary",
        "priority_score": 18,
        "surface_ids": (
            "stale_settlement_boundary",
            "nonce_replay_guard",
            "api_request_authorization_boundary",
        ),
        "what_if": "Balances, LP positions, fee values, or canonical state size are individually in range but compose into an oversized or noncanonical persistent state.",
        "disaster_state_template": "accounting-valid local update creates noncanonical or oversized state root",
        "mutation_families": (
            "balance and LP boundary values with canonical-size edge",
            "liquidity operation at fee and reserve BVA boundaries",
            "state serialization that passes local accounting but fails canonical size limits",
        ),
        "bounded_harness_ideas": (
            "run balances, LP, canonical size, liquidity, and fee BVA tests as one accounting boundary lane",
            "treat state-root noncanonicality after an accepted accounting update as a disaster state",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/state/test_balances.py",
                "tests/state/test_lp.py",
                "tests/state/test_canonical_size_bounds.py",
                "tests/core/test_liquidity.py",
                "tests/core/test_fees_bva.py",
            ),
        ),
    },
    {
        "axis_id": "zusd_api_token_policy_surface",
        "priority_score": 16,
        "surface_ids": (
            "api_request_authorization_boundary",
            "settlement_attestation_policy_boundary",
            "nonce_replay_guard",
        ),
        "what_if": "zUSD API, Tau token, wallet, or multi-vault operation surfaces accept a token action whose oracle or policy root belongs to a neighboring state.",
        "disaster_state_template": "zUSD token/API policy-valid action executes under stale oracle or wallet authority",
        "mutation_families": (
            "wallet command replay with changed token policy context",
            "zUSD API request at oracle-policy boundary",
            "multi-vault action whose token/Tau witness belongs to a stale vault state",
        ),
        "bounded_harness_ideas": (
            "combine zUSD API, Tau token, wallet CLI, and core zUSD multi tests",
            "reject every token action whose API authority and oracle policy roots do not match current state",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/integration/test_zusd_api.py",
                "tests/integration/test_zusd_tau_token.py",
                "tests/integration/test_zusd_tau_wallet_cli.py",
                "tests/core/test_zusd.py",
                "tests/core/test_zusd_multi.py",
            ),
        ),
    },
    {
        "axis_id": "dex_engine_sequence_anomaly_surface",
        "priority_score": 14,
        "surface_ids": (
            "stale_settlement_boundary",
            "stale_quote_receipt_boundary",
            "nonce_replay_guard",
        ),
        "what_if": "A multi-step DEX engine sequence is locally accepted by helper paths but produces an anomaly once quote receipts, settlement, and nonce effects interleave.",
        "disaster_state_template": "engine sequence grammar finds accepted state with anomaly or stale witness reuse",
        "mutation_families": (
            "valid engine operation followed by stale quote receipt and settlement replay",
            "helper-generated operation sequence whose anomaly detector sees drift",
            "pipeline operation ordering that preserves syntax but changes side-effect order",
        ),
        "bounded_harness_ideas": (
            "run engine sequence grammar, engine integration, helpers, anomaly, and pipeline tests together",
            "treat accepted anomaly-tagged engine state as a disaster witness",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/integration/test_dex_engine_sequence_grammar_fuzz.py",
                "tests/integration/test_dex_engine.py",
                "tests/integration/test_dex_engine_helpers.py",
                "tests/integration/test_dex_engine_anomaly.py",
                "tests/integration/test_dex_pipeline.py",
            ),
        ),
    },
    {
        "axis_id": "quote_receipt_gate_decomposition_consistency",
        "priority_score": 12,
        "surface_ids": (
            "quote_receipt_transport_boundary",
            "quote_receipt_certificate_boundary",
            "stale_quote_receipt_boundary",
        ),
        "what_if": "Each quote-receipt sub-gate rejects its local mutation, but a decomposed receipt moves a malformed field across gate boundaries and survives composition.",
        "disaster_state_template": "sub-gate-valid quote receipt composes into an invalid executable receipt",
        "mutation_families": (
            "precheck-success with certificate-body drift",
            "hop replay mismatch hidden by leg-summary repair",
            "pool snapshot and totals gates disagree on the rejected field",
        ),
        "bounded_harness_ideas": (
            "run every quote-receipt native gate and receipt fuzz lane as one decomposed boundary",
            "minimize witnesses to the first gate whose reject token disappears under composition",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/core/test_quote_receipt_precheck_gate.py",
                "tests/core/test_quote_receipt_certificate_gate.py",
                "tests/core/test_quote_receipt_hop_replay_gate.py",
                "tests/core/test_quote_receipt_hop_structure_gate.py",
                "tests/core/test_quote_receipt_leg_summary_gate.py",
                "tests/core/test_quote_receipt_pool_snapshot_gate.py",
                "tests/core/test_quote_receipt_totals_gate.py",
                "tests/core/test_quote_receipts.py",
                "tests/core/test_quote_receipts_fuzz.py",
            ),
        ),
    },
    {
        "axis_id": "settlement_witness_lifecycle_value_drift",
        "priority_score": 10,
        "surface_ids": (
            "stale_settlement_boundary",
            "settlement_attestation_policy_boundary",
            "quote_receipt_certificate_boundary",
        ),
        "what_if": "A settlement witness remains lifecycle-valid while its value packet, LP value packet, or feature extension packet belongs to a stale economic context.",
        "disaster_state_template": "lifecycle-valid settlement witness hides stale or mismatched value semantics",
        "mutation_families": (
            "value contract replayed after witness lifecycle phase drift",
            "LP value packet mismatch under otherwise valid settlement witness",
            "feature-extension packet bound to a neighboring settlement root",
        ),
        "bounded_harness_ideas": (
            "pair witness lifecycle, region lifecycle, and settlement value packet tests",
            "reject every lifecycle-valid witness whose value packet cannot be recomputed from the same root",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/integration/test_settlement_witness_lifecycle.py",
                "tests/integration/test_settlement_witness_lifecycle_regions.py",
                "tests/integration/test_settlement_value_contract.py",
                "tests/integration/test_settlement_value_packet.py",
                "tests/integration/test_settlement_lp_value_contract.py",
                "tests/integration/test_settlement_endogenous_lp_value_packet.py",
                "tests/integration/test_settlement_feature_extension_packet.py",
            ),
        ),
    },
    {
        "axis_id": "dex_core_ref_parity_drift",
        "priority_score": 8,
        "surface_ids": (
            "stale_settlement_boundary",
            "stale_quote_receipt_boundary",
            "nonce_replay_guard",
        ),
        "what_if": "A DEX step is accepted by one runtime path while the kernel reference path reaches a different state, event, or candidate-set interpretation.",
        "disaster_state_template": "runtime/ref parity drift creates a replayable semantic fork",
        "mutation_families": (
            "candidate settlement accepted by helper but rejected by kernel ref",
            "v7/v8 reference parity drift at boundary reserves",
            "ML BVA parity edge where state and emitted event disagree",
        ),
        "bounded_harness_ideas": (
            "run DEX step and reference parity tests as a single fork-detection lane",
            "treat any runtime/ref mismatch as a disaster witness even when both paths are deterministic",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/core/test_dex_step.py",
                "tests/core/test_dex_step_candidate_settlement.py",
                "tests/core/test_dex_step_core_v2_ref_parity.py",
                "tests/core/test_dex_v7_ref_parity.py",
                "tests/core/test_dex_v8_ref_parity.py",
                "tests/core/test_dex_step_core_v2_ml_bva_parity.py",
            ),
        ),
    },
    {
        "axis_id": "confidential_request_admission_gate_decomposition",
        "priority_score": 6,
        "surface_ids": (
            "api_request_authorization_boundary",
            "quote_receipt_transport_boundary",
            "settlement_attestation_policy_boundary",
        ),
        "what_if": "A confidential request, live-admission gate, receipt precheck, and API wrapper disagree about whether evidence is current and usable.",
        "disaster_state_template": "confidential admission gate accepts stale or cross-context evidence",
        "mutation_families": (
            "request-use gate passes while live-admission edge rejects",
            "receipt precheck accepts body whose extension receipt fails",
            "API confidential request repairs one wrapper hash around stale evidence",
        ),
        "bounded_harness_ideas": (
            "compose confidential native adapters with API confidential regressions",
            "fail closed unless request-use, live-admission, receipt, and API wrapper all bind to the same evidence root",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/kernels/test_confidential_request_use_gate_v1_native_adapter.py",
                "tests/kernels/test_confidential_extension_live_admission_gate_v1_native_adapter.py",
                "tests/kernels/test_confidential_extension_receipt_gate_v1_native_adapter.py",
                "tests/kernels/test_confidential_extension_receipt_precheck_gate_v1_native_adapter.py",
                "tests/integration/test_api_server_confidential.py",
            ),
        ),
    },
    {
        "axis_id": "boundary_concolic_wrapper_consistency",
        "priority_score": 4,
        "surface_ids": (
            "api_request_authorization_boundary",
            "quote_receipt_transport_boundary",
            "nonce_replay_guard",
        ),
        "what_if": "Boundary-concolic wrappers for API, receipt, and state surfaces disagree about the normalized envelope for the same malformed or replayed input.",
        "disaster_state_template": "wrapper-valid malformed input reaches a neighboring state or receipt boundary",
        "mutation_families": (
            "API stateful wrapper normalization hides malformed receipt field",
            "receipt boundary mutation passes state boundary replay shape",
            "state boundary concolic seed becomes valid after API envelope repair",
        ),
        "bounded_harness_ideas": (
            "run stateless and stateful concolic wrappers for API, receipt, and state together",
            "promote cross-wrapper normalization disagreement into a minimized boundary witness",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/integration/test_api_server_boundary_concolic.py",
                "tests/integration/test_api_server_boundary_concolic_stateful.py",
                "tests/integration/test_receipt_boundary_concolic.py",
                "tests/integration/test_receipt_boundary_concolic_stateful.py",
                "tests/integration/test_state_boundary_concolic.py",
                "tests/integration/test_state_boundary_concolic_stateful.py",
                "tests/integration/test_boundary_concolic_determinism.py",
            ),
        ),
    },
    {
        "axis_id": "runtime_shell_adapter_consistency",
        "priority_score": 2,
        "surface_ids": (
            "stale_settlement_boundary",
            "route_canonicalization_boundary",
            "api_request_authorization_boundary",
        ),
        "what_if": "A kernel shell adapter has the right action/effect surface but is bound to a stale IR hash or diverges from interpreter traces.",
        "disaster_state_template": "adapter-valid runtime shell executes against a different kernel spec",
        "mutation_families": (
            "adapter IR hash drift after kernel spec update",
            "effect drain ordering mismatch between shell and interpreter",
            "native wrapper edge accepted while shell verification rejects",
        ),
        "bounded_harness_ideas": (
            "run shell lint, shell verification, spot-core adapters, Python wrappers, and native settlement adapter edges together",
            "treat IR-hash mismatch as a disaster-search failure until the adapter binding is refreshed",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/kernels/test_runtime_shell_adapters.py",
                "tests/kernels/test_spot_core_shell_adapters.py",
                "tests/kernels/test_python_adapter_wrappers.py",
                "tests/kernels/test_settlement_witness_native_adapter_edges.py",
            ),
        ),
    },
    {
        "axis_id": "perp_submission_surface_gate_composition",
        "priority_score": 1,
        "surface_ids": (
            "api_request_authorization_boundary",
            "settlement_attestation_policy_boundary",
            "operations_signature_reuse_boundary",
        ),
        "what_if": "Perps submission auth, signed-surface, market-version, and runtime-risk gates each reject locally but a cross-gate payload reaches the wrong reducer.",
        "disaster_state_template": "perps submission surface admits an action under the wrong signed, market, or risk context",
        "mutation_families": (
            "signed surface valid with stale market version prefix",
            "field-selector auth accepts a neighboring submission message",
            "runtime risk gate and Tau ingress stream disagree on admissibility",
        ),
        "bounded_harness_ideas": (
            "compose submission auth, field selector, signed surface, market version, runtime risk, and Tau ingress tests",
            "treat any cross-gate disagreement that reaches reducer dispatch as a disaster state",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/core/test_perp_clearinghouse_market_params_guard.py",
                "tests/core/test_perp_market_version_prefix_guard.py",
                "tests/core/test_perp_runtime_risk_gate.py",
                "tests/core/test_perp_signed_surface_guard.py",
                "tests/core/test_perp_submission_auth_field_selector_gate.py",
                "tests/core/test_perp_submission_auth_gate.py",
                "tests/core/test_perp_submission_auth_message.py",
                "tests/core/test_perp_tau_ingress_stream.py",
            ),
        ),
    },
    {
        "axis_id": "perp_v2_ref_oracle_parity_boundary",
        "priority_score": 0,
        "surface_ids": (
            "settlement_attestation_policy_boundary",
            "stale_settlement_boundary",
            "api_request_authorization_boundary",
        ),
        "what_if": "Native perps v2, generated references, and oracle-equivalence checks disagree at boundary epochs or partial-liquidation edges.",
        "disaster_state_template": "perps native/ref fork admits stale oracle settlement or divergent liquidation state",
        "mutation_families": (
            "engine BVA edge with oracle equivalence drift",
            "generated reference parity mismatch after partial liquidation",
            "invariant-preserving state whose native and reference events disagree",
        ),
        "bounded_harness_ideas": (
            "run engine BVA, oracle equivalence, generated-reference parity, partial liquidation, and invariants together",
            "treat native/ref state or event divergence as a semantic fork witness",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/core/test_perp_v2/test_engine_boundary_bva.py",
                "tests/core/test_perp_v2/test_oracle_equiv.py",
                "tests/core/test_perp_v2/test_parity_with_generated_ref.py",
                "tests/core/test_perp_v2/test_partial_liquidate.py",
                "tests/core/test_perp_v2/test_invariants.py",
            ),
        ),
    },
    {
        "axis_id": "exact_out_prefilter_winner_repair_boundary",
        "priority_score": -1,
        "surface_ids": (
            "route_canonicalization_boundary",
            "quote_receipt_certificate_boundary",
            "api_request_authorization_boundary",
        ),
        "what_if": "Exact-out prefilters, projection covers, and repaired winner packets agree locally but omit the true canonical winner after repair.",
        "disaster_state_template": "prefilter-valid exact-out packet certifies a noncanonical or unsupported winner",
        "mutation_families": (
            "prefilter support witness drops a feasible winner",
            "contraction audit passes while projection cover misses a branch",
            "repaired prefilter packet changes the certified winner key",
        ),
        "bounded_harness_ideas": (
            "run prefilter subset search, repaired prefilter, support/contraction/projection audits, and certified-winner packets together",
            "treat any repaired packet whose winner is not covered by the emitted domain as a disaster witness",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/core/test_exact_out_many_pool_certified_winner_packet_v1_adapter.py",
                "tests/core/test_exact_out_many_pool_prefilter_subset_search_v1.py",
                "tests/core/test_exact_out_many_pool_repaired_prefilter_v1.py",
                "tests/core/test_exact_out_many_pool_prefilter_support_audit_v1.py",
                "tests/core/test_exact_out_many_pool_prefilter_contraction_audit_v1.py",
                "tests/core/test_exact_out_many_pool_projection_cover_audit_v1.py",
                "tests/core/test_exact_out_route_canonical_selector_v1.py",
            ),
        ),
    },
    {
        "axis_id": "batch_refinement_mci_parity_boundary",
        "priority_score": -2,
        "surface_ids": (
            "stale_settlement_boundary",
            "route_canonicalization_boundary",
            "quote_receipt_certificate_boundary",
        ),
        "what_if": "Batch clearing refinement, greedy/MCI helpers, and settler reference parity each pass but select different accepted normal forms.",
        "disaster_state_template": "batch-refinement-valid settlement changes canonical fill or surplus semantics",
        "mutation_families": (
            "B-refinement witness with changed greedy ordering",
            "MCI tie where ref parity and runtime choose different canonical order",
            "coverage edge that preserves volume but changes surplus witness",
        ),
        "bounded_harness_ideas": (
            "pair batch ref parity, B-refinement, coverage edges, greedy, and MCI tests",
            "treat equal-volume/non-equal-surplus disagreement as a canonicalization disaster",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/core/test_batch_auction_settler_v1_ref_parity.py",
                "tests/core/test_batch_clearing_b_refinement.py",
                "tests/core/test_batch_clearing_coverage_edges.py",
                "tests/core/test_batch_greedy.py",
                "tests/core/test_batch_mci.py",
            ),
        ),
    },
    {
        "axis_id": "agent_policy_signing_artifact_boundary",
        "priority_score": -3,
        "surface_ids": (
            "api_request_authorization_boundary",
            "operations_signature_reuse_boundary",
            "nonce_replay_guard",
        ),
        "what_if": "A local user policy, compiled artifact, Tau adapter, or intent signer preflight signs one policy shape but runtime consumes another.",
        "disaster_state_template": "policy/signature artifact authorizes a neighboring action shape",
        "mutation_families": (
            "intent signer preflight passes with policy artifact drift",
            "policy text compiler emits artifact whose local policy root differs",
            "Tau policy adapter accepts a signed bundle under a stale user rule",
        ),
        "bounded_harness_ideas": (
            "run signer preflight/signing, local policy, policy artifacts, compilers, and Tau adapter together",
            "reject every signed policy artifact not bound to the current local policy root and intent shape",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/agents/test_intent_signer_pokayoke_preflight.py",
                "tests/agents/test_intent_signer_signing.py",
                "tests/agents/test_local_policy.py",
                "tests/agents/test_policy_artifacts.py",
                "tests/agents/test_policy_compiler.py",
                "tests/agents/test_policy_text_compiler.py",
                "tests/agents/test_tau_policy_adapter.py",
            ),
        ),
    },
    {
        "axis_id": "tau_runner_api_lifecycle_fail_closed",
        "priority_score": -4,
        "surface_ids": (
            "api_request_authorization_boundary",
            "settlement_attestation_policy_boundary",
            "operations_signature_reuse_boundary",
        ),
        "what_if": "Tau runner failures, proof-mining status requests, or API startup paths degrade from fail-closed into optimistic admission.",
        "disaster_state_template": "runtime lifecycle failure silently weakens API or Tau execution gating",
        "mutation_families": (
            "Tau runner chaos returns a syntactically valid but unusable result",
            "API main lifecycle starts proof-mining status with missing verifier state",
            "proof-mining status reports enabled while underlying proof path is unavailable",
        ),
        "bounded_harness_ideas": (
            "use no-skip Tau runner chaos and API lifecycle tests as a fail-closed lane",
            "keep TauNet client chaos with skips outside unreachable receipts until external dependency coverage is available",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/chaos/test_tau_runner_chaos.py",
                "tests/integration/test_api_server_main.py",
                "tests/integration/test_api_server_proof_mining_status.py",
            ),
        ),
    },
    {
        "axis_id": "fire_runtime_receipt_replay_boundary",
        "priority_score": -5,
        "surface_ids": (
            "settlement_attestation_policy_boundary",
            "stale_settlement_boundary",
            "quote_receipt_certificate_boundary",
        ),
        "what_if": "FIRE runtime notes and kernel receipts validate individually but replay under a stale kernel, settlement, or compile receipt.",
        "disaster_state_template": "FIRE receipt-valid artifact replays against a different runtime kernel contract",
        "mutation_families": (
            "burn-boost runtime note with stale kernel eval receipt",
            "fee note or LP-loss-cover runtime accepted under different replay receipt",
            "kernel settlement receipt mismatch after compile or kernel-root drift",
        ),
        "bounded_harness_ideas": (
            "run FIRE runtime note tests with kernel eval, receipt, replay, and settlement receipt CLI checks",
            "reject every replay whose kernel receipt root differs from the current runtime artifact",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/core/test_fire_burn_boost_call_v1_runtime.py",
                "tests/core/test_fire_fee_note_v1_runtime.py",
                "tests/core/test_fire_lp_loss_cover_v1_runtime.py",
                "tests/integration/test_check_fire_kernel_eval_receipt_cli.py",
                "tests/integration/test_check_fire_kernel_receipt_cli.py",
                "tests/integration/test_check_fire_kernel_replay_receipt_cli.py",
                "tests/integration/test_check_fire_kernel_settlement_receipt_cli.py",
            ),
        ),
    },
    {
        "axis_id": "exact_in_route_certificate_guarded_key_boundary",
        "priority_score": -6,
        "surface_ids": (
            "route_canonicalization_boundary",
            "quote_receipt_certificate_boundary",
            "api_request_authorization_boundary",
        ),
        "what_if": "Exact-in route certificates, guarded quote packets, and core routing selectors disagree about the true canonical key after mixed-split or exact-out gate interactions.",
        "disaster_state_template": "exact-in certificate-valid route is not the runtime canonical route",
        "mutation_families": (
            "mixed direct/two-hop split at amount boundary",
            "guarded quote packet whose true-key interpretation disagrees with runtime selector",
            "exact-out gate edge that changes exact-in candidate ordering",
        ),
        "bounded_harness_ideas": (
            "run exact-in certificate/fuzz, ESSO guarded/true-key packets, and routing exact-out gate tests together",
            "treat runtime/certificate canonical-key disagreement as a route disaster witness",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/integration/test_exact_in_route_certificate.py",
                "tests/integration/test_exact_in_route_certificate_fuzz.py",
                "tests/formal/test_esso_exact_in_route_guarded_quote_packet.py",
                "tests/formal/test_esso_exact_in_route_true_key_interpretation_packet.py",
                "tests/core/test_routing.py",
                "tests/core/test_routing_exact_out.py",
                "tests/core/test_routing_exact_out_gate.py",
            ),
        ),
    },
    {
        "axis_id": "quote_receipt_transport_intent_boundary",
        "priority_score": -7,
        "surface_ids": (
            "quote_receipt_transport_boundary",
            "quote_receipt_certificate_boundary",
            "nonce_replay_guard",
        ),
        "what_if": "Quote receipt intent binding, transport grammar, and sequence grammar each pass but accept a receipt under the wrong intent or transport envelope.",
        "disaster_state_template": "transport-valid quote receipt executes under a neighboring intent binding",
        "mutation_families": (
            "receipt intent id preserved while transport envelope changes",
            "sequence grammar repairs receipt hash around stale intent fields",
            "transport grammar accepts an equivalent-looking but noncanonical receipt body",
        ),
        "bounded_harness_ideas": (
            "run quote receipt intents, sequence grammar, and transport grammar together",
            "reject every transport receipt whose intent and body roots do not match the same canonical envelope",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/integration/test_quote_receipt_intents.py",
                "tests/integration/test_quote_receipt_sequence_grammar_fuzz.py",
                "tests/integration/test_quote_receipt_transport_grammar_fuzz.py",
            ),
        ),
    },
    {
        "axis_id": "oracle_funding_clock_commitment_boundary",
        "priority_score": -8,
        "surface_ids": (
            "settlement_attestation_policy_boundary",
            "stale_settlement_boundary",
            "api_request_authorization_boundary",
        ),
        "what_if": "Epoch oracle commitments, oracle freshness BVA, and funding-rate settlement clocks disagree about which price/time snapshot is usable.",
        "disaster_state_template": "clock-valid funding or oracle commitment applies under a stale or neighboring epoch",
        "mutation_families": (
            "oracle commitment at freshness boundary but funding market sees stale clock",
            "funding-rate ref parity differs after settlement runtime clock advance",
            "oracle freshness BVA edge admitted by one consumer and rejected by another",
        ),
        "bounded_harness_ideas": (
            "run epoch oracle commitment, oracle freshness BVA, funding market, ref parity, and runtime settlement together",
            "fail closed whenever oracle/funding consumers disagree on the same committed epoch",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/core/test_epoch_oracle_commitment.py",
                "tests/core/test_oracle_freshness_bva.py",
                "tests/core/test_funding_rate_market.py",
                "tests/core/test_funding_rate_market_ref_parity.py",
                "tests/core/test_funding_rate_settlement_runtime_v1_1.py",
            ),
        ),
    },
    {
        "axis_id": "intent_normal_form_nonce_gate_boundary",
        "priority_score": -9,
        "surface_ids": (
            "nonce_replay_guard",
            "operations_signature_reuse_boundary",
            "api_request_authorization_boundary",
        ),
        "what_if": "Intent normal-form canonicalization and nonce sender/batch/sequence gates disagree about the signer or replay domain for equivalent-looking intents.",
        "disaster_state_template": "normal-form-valid intent aliases into a different nonce or sender gate",
        "mutation_families": (
            "intent normal form changes dead fields but preserves nonce root",
            "sender resolution gate accepts a neighboring canonical intent",
            "batch policy and sequence gate disagree after normal-form repair",
        ),
        "bounded_harness_ideas": (
            "compose intent normal form with nonce batch, sender resolution, and sequence state gates",
            "treat normal-form equality without nonce-domain equality as a replay disaster",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/core/test_intent_normal_form.py",
                "tests/state/test_intent_nonce_batch_policy_gate.py",
                "tests/state/test_intent_nonce_sender_resolution_gate.py",
                "tests/state/test_intent_nonce_sequence_gate.py",
            ),
        ),
    },
    {
        "axis_id": "zenograph_krr_policy_state_boundary",
        "priority_score": -10,
        "surface_ids": (
            "api_request_authorization_boundary",
            "operations_signature_reuse_boundary",
            "settlement_attestation_policy_boundary",
        ),
        "what_if": "Zenograph/KRR facts, rules, selectors, and policy history validate in isolation but select a policy from a stale fact store or microtheory.",
        "disaster_state_template": "policy-state-valid selector authorizes stale or unrelated factual context",
        "mutation_families": (
            "fact pack replayed after KRR policy history update",
            "microtheory/rule store drift with unchanged selector output",
            "schema-valid Zenograph store whose selected policy root differs from the signed policy",
        ),
        "bounded_harness_ideas": (
            "run KRR advisor/history and Zenograph fact/rule/schema/selector/store tests together",
            "reject policy selection unless fact pack, microtheory, rules, schema, and store roots are current",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/agents/test_krr_policy_advisor.py",
                "tests/agents/test_krr_policy_history.py",
                "tests/agents/test_zenograph_fact_pack.py",
                "tests/agents/test_zenograph_microtheories.py",
                "tests/agents/test_zenograph_rules.py",
                "tests/agents/test_zenograph_schema.py",
                "tests/agents/test_zenograph_selector.py",
                "tests/agents/test_zenograph_store.py",
            ),
        ),
    },
    {
        "axis_id": "zusd_native_accounting_gate_boundary",
        "priority_score": -11,
        "surface_ids": (
            "stale_settlement_boundary",
            "api_request_authorization_boundary",
            "settlement_attestation_policy_boundary",
        ),
        "what_if": "zUSD mint, redeem, repay, withdraw, liquidation, risky-op, and oracle-commit native gates agree locally but compose into stale collateral accounting.",
        "disaster_state_template": "native zUSD accounting gate admits stale or double-counted collateral/debt state",
        "mutation_families": (
            "mint/redeem fee gate edge with stale oracle commit",
            "repay/withdraw/liquidation sequence whose coverage edge preserves syntax but changes debt",
            "risky-op gate accepts after native accounting state drift",
        ),
        "bounded_harness_ideas": (
            "run zUSD coverage edges and native accounting/risky/oracle gate adapters together",
            "reject every native gate composition whose debt/collateral root cannot be recomputed from current state",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/core/test_zusd_coverage_edges.py",
                "tests/kernels/test_zusd_mint_borrow_fee_v1_native_adapter.py",
                "tests/kernels/test_zusd_redeem_fee_collateral_v1_native_adapter.py",
                "tests/kernels/test_zusd_repay_single_vault_v1_native_adapter.py",
                "tests/kernels/test_zusd_withdraw_collateral_apply_v1_native_adapter.py",
                "tests/kernels/test_zusd_liquidation_sp_absorb_v1_native_adapter.py",
                "tests/kernels/test_zusd_risky_ops_gate_v1_native_adapter.py",
                "tests/kernels/test_zusd_oracle_commit_apply_v1_native_adapter.py",
            ),
        ),
    },
    {
        "axis_id": "proof_mining_manager_slot_control_boundary",
        "priority_score": -12,
        "surface_ids": (
            "api_request_authorization_boundary",
            "nonce_replay_guard",
            "operations_signature_reuse_boundary",
        ),
        "what_if": "Proof-mining manager state, claimability, slot assignment, and submit-command args validate separately but admit a stale or unauthorized claim slot.",
        "disaster_state_template": "slot-valid proof-mining manager state pays or reserves the wrong claimant",
        "mutation_families": (
            "claimability gate passes after manager slot assignment drift",
            "submit-command args shape valid but bound to stale slot state",
            "manager native adapter accepts a replayed slot assignment",
        ),
        "bounded_harness_ideas": (
            "run manager, claimability, slot assignment, submit args, and native adapters together",
            "reject every claim whose manager state and slot assignment do not share the same current root",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/core/test_proof_mining_manager.py",
                "tests/core/test_proof_mining_claimability_gate.py",
                "tests/core/test_proof_mining_slot_assignment_gate.py",
                "tests/core/test_proof_mining_manager_submit_command_args_gate.py",
                "tests/kernels/test_proof_mining_claimability_gate_v1_native_adapter.py",
                "tests/kernels/test_proof_mining_slot_assignment_gate_v1_native_adapter.py",
                "tests/kernels/test_proof_mining_manager_submit_command_args_gate_v1_native_adapter.py",
            ),
        ),
    },
    {
        "axis_id": "strategy_native_policy_guard_surface",
        "priority_score": -13,
        "surface_ids": (
            "api_request_authorization_boundary",
            "operations_signature_reuse_boundary",
            "settlement_attestation_policy_boundary",
        ),
        "what_if": "Autotrader strategy native guards validate budget, candidate set, signal provenance, signer binding, and submit envelopes separately but compose into a stale or unauthorized strategy action.",
        "disaster_state_template": "strategy guard-valid action executes under stale signal, signer, or policy context",
        "mutation_families": (
            "candidate-set contract passes while route economic sanity fails",
            "signal provenance root changes after signer binding",
            "submit bundle accepted with stale observation or wallet outbound guard",
        ),
        "bounded_harness_ideas": (
            "run all strategy native guard adapters as a single policy-surface lane",
            "reject every strategy action unless budget, candidate set, signal, signer, wallet, and submit roots share the same current context",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/core/test_strategy_budget_guard_v1_adapter.py",
                "tests/core/test_strategy_candidate_set_contract_v1_adapter.py",
                "tests/core/test_strategy_compilation_witness_v1_adapter.py",
                "tests/core/test_strategy_compile_contract_v1_adapter.py",
                "tests/core/test_strategy_emit_finalize_v1_adapter.py",
                "tests/core/test_strategy_execution_guard_v1_adapter.py",
                "tests/core/test_strategy_external_signal_contract_v1_adapter.py",
                "tests/core/test_strategy_external_signal_source_registry_guard_v1_adapter.py",
                "tests/core/test_strategy_live_admission_bundle_v1_adapter.py",
                "tests/core/test_strategy_observation_packet_contract_v1_adapter.py",
                "tests/core/test_strategy_signal_provenance_guard_v1_adapter.py",
                "tests/core/test_strategy_signer_binding_guard_v1_adapter.py",
                "tests/core/test_strategy_submit_bundle_guard_v1_adapter.py",
                "tests/core/test_strategy_system_compose_v1_adapter.py",
                "tests/core/test_strategy_tx_envelope_guard_v1_adapter.py",
            ),
        ),
    },
    {
        "axis_id": "autotrader_policy_toolchain_state_boundary",
        "priority_score": -14,
        "surface_ids": (
            "api_request_authorization_boundary",
            "operations_signature_reuse_boundary",
            "nonce_replay_guard",
        ),
        "what_if": "Autotrader local guards, user rules, KRR bundles, strategy IR, controller, multi-action decisions, and shadow tools each pass but disagree about the policy state being executed.",
        "disaster_state_template": "toolchain-valid autotrader policy emits action from stale or mismatched strategy state",
        "mutation_families": (
            "local guard evaluator uses stale user rule bundle",
            "strategy IR compiled from one policy but shadow CLI replays another",
            "multi-action decision accepts a KRR bundle root from a neighboring policy history",
        ),
        "bounded_harness_ideas": (
            "compose local guard, Q-learning sandbox, user rule, KRR bundle, strategy IR, controller, decision, compiler, and shadow tests",
            "treat policy-toolchain root disagreement as a replayable automation disaster",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/agents/test_autotrader_local_guard_evaluator.py",
                "tests/agents/test_autotrader_q_learning_sandbox.py",
                "tests/agents/test_autotrader_user_rule_bundle.py",
                "tests/agents/test_krr_bundle_artifacts.py",
                "tests/agents/test_strategy_ir.py",
                "tests/integration/test_autotrader_controller.py",
                "tests/integration/test_autotrader_multiaction_decision.py",
                "tests/integration/test_autotrader_policy_compile_cli.py",
                "tests/integration/test_autotrader_q_learning_sandbox_cli.py",
                "tests/integration/test_autotrader_shadow_cli.py",
            ),
        ),
    },
    {
        "axis_id": "confidential_core_verifier_binding_boundary",
        "priority_score": -15,
        "surface_ids": (
            "quote_receipt_transport_boundary",
            "api_request_authorization_boundary",
            "settlement_attestation_policy_boundary",
        ),
        "what_if": "Confidential core admission, receipt gates, and the attestation verifier accept the same wrapper under different live-admission or receipt-precheck roots.",
        "disaster_state_template": "confidential core-valid wrapper admits stale verifier evidence",
        "mutation_families": (
            "live admission passes while receipt precheck rejects",
            "receipt gate accepts evidence that verifier binds to a different report",
            "core admission changes feature status after verifier result is built",
        ),
        "bounded_harness_ideas": (
            "run confidential core gates and attestation verifier tests together",
            "fail closed unless core admission, receipt gates, and verifier evidence all bind to the same current report root",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/core/test_confidential_extension_live_admission.py",
                "tests/core/test_confidential_extension_live_admission_gate.py",
                "tests/core/test_confidential_extension_receipt_gate.py",
                "tests/core/test_confidential_extension_receipt_precheck_gate.py",
                "tests/integration/test_confidential_attestation_verifier.py",
            ),
        ),
    },
    {
        "axis_id": "cantor_shapeforge_morphism_bridge_boundary",
        "priority_score": -16,
        "surface_ids": (
            "stale_settlement_boundary",
            "route_canonicalization_boundary",
            "api_request_authorization_boundary",
        ),
        "what_if": "Cantor partitions, morphism receipts, product regions, and Shapeforge bridge reports validate independently but promote a stale or wrong partition morphism.",
        "disaster_state_template": "partition/morphism-valid bridge promotes a stale world-model shape",
        "mutation_families": (
            "backend invariance receipt valid after morphism product drift",
            "Cantor product receipt replayed under a neighboring prefix algebra",
            "Shapeforge bridge report verifies while promotion root belongs to stale partition evidence",
        ),
        "bounded_harness_ideas": (
            "split slow Cantor/Shapeforge checks into replayable commands below the disaster-runner timeout",
            "reject bridge promotion unless region assurance, backend invariance, morphism receipts, products, and Shapeforge roots match",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/integration/test_build_cantor_region_assurance_bundle.py",
                "tests/integration/test_build_cantor_region_backend_invariance_receipt.py",
                "tests/integration/test_check_cantor_region_assurance_bundle.py",
                "tests/integration/test_check_cantor_region_backend_invariance.py",
                "tests/integration/test_check_cantor_region_backend_invariance_receipt.py",
            ),
            (
                "pytest",
                "-q",
                "tests/integration/test_cantor_bdd_region.py",
                "tests/integration/test_cantor_prefix_algebra.py",
                "tests/integration/test_cantor_region_morphism_receipts.py",
                "tests/integration/test_cantor_region_morphisms.py",
                "tests/integration/test_cantor_region_products.py",
            ),
            (
                "pytest",
                "-q",
                "tests/integration/test_build_cantor_shapeforge_bridge_report.py",
                "tests/integration/test_cantor_shapeforge_bridge_report.py",
                "tests/integration/test_check_cantor_shapeforge_bridge_report.py",
            ),
            (
                "pytest",
                "-q",
                "tests/integration/test_cantor_shapeforge_bridge_verify.py",
                "tests/integration/test_check_cantor_shapeforge_promotion.py",
            ),
        ),
    },
    {
        "axis_id": "fire_cli_supply_chain_receipt_boundary",
        "priority_score": -17,
        "surface_ids": (
            "settlement_attestation_policy_boundary",
            "stale_settlement_boundary",
            "quote_receipt_certificate_boundary",
        ),
        "what_if": "FIRE compile receipts, ESSO kernel checks, object packages, proof-tree certs, registry bundles, and settlement replay gates validate different package roots.",
        "disaster_state_template": "FIRE supply-chain-valid CLI artifact replays under a mismatched package or registry root",
        "mutation_families": (
            "compile receipt valid while object package root changes",
            "proof-tree certificate uses stale registry bundle",
            "settlement replay gate accepts a settlement apply report from a neighboring kernel receipt",
        ),
        "bounded_harness_ideas": (
            "compose FIRE compile, ESSO, FMOS, object package, proof tree, registry, settlement report, replay gate, ZPL compile, and apply CLIs",
            "reject every FIRE settlement artifact whose package, registry, proof, and replay roots do not agree",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/integration/test_check_fire_compile_receipt_cli.py",
                "tests/integration/test_check_fire_esso_kernels_cli.py",
                "tests/integration/test_check_fire_fmos_spec_cli.py",
                "tests/integration/test_check_fire_object_package_cli.py",
                "tests/integration/test_check_fire_proof_tree_cert_cli.py",
                "tests/integration/test_check_fire_registry_bundle_cli.py",
                "tests/integration/test_check_fire_settlement_apply_report_cli.py",
                "tests/integration/test_check_fire_settlement_replay_gate_cli.py",
                "tests/integration/test_compile_fire_zpl_cli.py",
                "tests/integration/test_apply_fire_settlement_cli.py",
                "tests/integration/test_build_fire_registry_bundle_cli.py",
            ),
        ),
    },
    {
        "axis_id": "settlement_formal_packet_contract_boundary",
        "priority_score": -18,
        "surface_ids": (
            "stale_settlement_boundary",
            "settlement_attestation_policy_boundary",
            "quote_receipt_certificate_boundary",
        ),
        "what_if": "Settlement ESSO packet contracts and witness lifecycle checks pass independently but disagree about spot price, value, LP, feature extension, or lifecycle roots.",
        "disaster_state_template": "formal settlement packet-valid witness hides mismatched value or lifecycle root",
        "mutation_families": (
            "spot price packet and value contract bind different roots",
            "LP value contract valid while endogenous LP packet drifts",
            "witness lifecycle proof accepts a stale feature-extension packet",
        ),
        "bounded_harness_ideas": (
            "run settlement ESSO packet contracts and lifecycle tests together",
            "fail closed unless spot, value, LP, feature, end-to-end, and lifecycle roots are identical",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/formal/test_esso_settlement_end_to_end_certificate_packet.py",
                "tests/formal/test_esso_settlement_endogenous_lp_value_packet.py",
                "tests/formal/test_esso_settlement_feature_extension_packet.py",
                "tests/formal/test_esso_settlement_lp_value_contract.py",
                "tests/formal/test_esso_settlement_spot_price_attestation.py",
                "tests/formal/test_esso_settlement_spot_price_packet.py",
                "tests/formal/test_esso_settlement_spot_value_contract.py",
                "tests/formal/test_esso_settlement_value_packet.py",
                "tests/formal/test_esso_settlement_witness_lifecycle_v1.py",
                "tests/formal/test_settlement_witness_lifecycle_v1.py",
            ),
        ),
    },
    {
        "axis_id": "exact_out_formal_packet_contract_boundary",
        "priority_score": -19,
        "surface_ids": (
            "route_canonicalization_boundary",
            "quote_receipt_certificate_boundary",
            "api_request_authorization_boundary",
        ),
        "what_if": "Exact-out ESSO candidate-domain, certified-winner, guarded-quote, prefilter, repaired-advisory, and repaired-prefilter packets validate incompatible route domains.",
        "disaster_state_template": "formal exact-out packet-valid route omits or miscertifies the canonical candidate domain",
        "mutation_families": (
            "candidate-domain contract valid but certified-winner packet uses different domain",
            "guarded quote packet repairs advisory output outside the prefilter contract",
            "repaired prefilter contract passes while repaired advisory packet changes winner semantics",
        ),
        "bounded_harness_ideas": (
            "run exact-out ESSO packet contracts as a formal candidate-domain language lane",
            "reject every exact-out packet unless candidate domain, prefilter, guarded quote, advisory repair, and winner roots agree",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/formal/test_esso_exact_out_many_pool_candidate_domain_contract.py",
                "tests/formal/test_esso_exact_out_many_pool_certified_winner_packet.py",
                "tests/formal/test_esso_exact_out_many_pool_guarded_quote_packet.py",
                "tests/formal/test_esso_exact_out_many_pool_prefilter_contract.py",
                "tests/formal/test_esso_exact_out_many_pool_repaired_advisory_quote_packet.py",
                "tests/formal/test_esso_exact_out_many_pool_repaired_prefilter_contract.py",
            ),
        ),
    },
    {
        "axis_id": "strategy_residual_guard_binding_boundary",
        "priority_score": -20,
        "surface_ids": (
            "api_request_authorization_boundary",
            "operations_signature_reuse_boundary",
            "settlement_attestation_policy_boundary",
        ),
        "what_if": "Residual strategy guards for oracle freshness, policy contracts, route economics, session state, wallet outflow, and Tau route-sanity witnesses validate different strategy contexts.",
        "disaster_state_template": "strategy residual guard-valid action executes under stale oracle, session, or wallet policy context",
        "mutation_families": (
            "route economic sanity witness accepts after policy contract root drift",
            "session state guard passes while wallet outbound guard binds a neighboring capability",
            "oracle freshness guard accepts a strategy observation from a stale context",
        ),
        "bounded_harness_ideas": (
            "compose residual strategy adapters with the Tau route economic sanity witness lane",
            "reject every strategy action unless oracle, policy, route, session, and wallet roots agree",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/core/test_strategy_oracle_freshness_guard_v1_adapter.py",
                "tests/core/test_strategy_policy_contracts_v1_adapter.py",
                "tests/core/test_strategy_route_economic_sanity_guard_v1_adapter.py",
                "tests/core/test_strategy_session_state_guard_v1_adapter.py",
                "tests/core/test_strategy_wallet_outbound_guard_v1_adapter.py",
                "tests/integration/test_tau_witness_autotrader_route_economic_sanity_guard.py",
            ),
        ),
    },
    {
        "axis_id": "perp_core_legacy_ref_hazard_boundary",
        "priority_score": -21,
        "surface_ids": (
            "settlement_attestation_policy_boundary",
            "stale_settlement_boundary",
            "api_request_authorization_boundary",
        ),
        "what_if": "Legacy clearinghouse refs, isolated epoch adapters, math hazards, funding rules, and v2 state invariants disagree about a perps transition near oracle or liquidation boundaries.",
        "disaster_state_template": "perps core/ref-valid transition hides stale oracle or divergent hazard accounting",
        "mutation_families": (
            "legacy clearinghouse ref accepts a transition whose isolated epoch adapter rejects",
            "math hazard boundary changes funding or liquidation eligibility",
            "perps v2 state invariant survives while submodule event accounting diverges",
        ),
        "bounded_harness_ideas": (
            "run perps legacy refs, isolated epoch adapter, hazard, funding, math, state, and submodule tests together",
            "treat native/ref disagreement as a disaster witness even when each reducer is locally deterministic",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/core/test_perp_clearinghouse_2p/test_ref_smoke.py",
                "tests/core/test_perp_clearinghouse_3p_transfer/test_ref_smoke.py",
                "tests/core/test_perp_epoch_default_adapter.py",
                "tests/core/test_perp_epoch_isolated_v1.py",
                "tests/core/test_perp_incentive_hazards.py",
                "tests/core/test_perp_math_hazards.py",
                "tests/core/test_perp_v2/test_funding_rule.py",
                "tests/core/test_perp_v2/test_math.py",
                "tests/core/test_perp_v2/test_state.py",
                "tests/core/test_perp_v2/test_submodules.py",
            ),
        ),
    },
    {
        "axis_id": "perp_engine_integration_oracle_bootstrap_boundary",
        "priority_score": -22,
        "surface_ids": (
            "settlement_attestation_policy_boundary",
            "stale_settlement_boundary",
            "operations_signature_reuse_boundary",
        ),
        "what_if": "Perps integration fixtures, runtime gates, signed surfaces, API wrappers, and market-parameter reducers bootstrap the first settlement without the same usable oracle snapshot.",
        "disaster_state_template": "operator-valid perps settlement proceeds under missing or mismatched initial oracle bootstrap",
        "mutation_families": (
            "first clearing-price publish followed by settle with no usable oracle snapshot",
            "runtime gate accepts while signed surface or market params bind a stale oracle epoch",
            "perps API admission changes oracle bootstrap semantics compared with engine integration",
        ),
        "bounded_harness_ideas": (
            "compose perps engine, runtime gate, signed surface, op-auth parity, market params, and API integration tests",
            "fail closed unless the initial settlement path has an explicit usable oracle snapshot before PnL realization",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/integration/test_perp_engine.py",
                "tests/integration/test_perp_engine_clearinghouse_2p.py",
                "tests/integration/test_perp_engine_clearinghouse_3p_transfer.py",
                "tests/integration/test_perp_engine_market_params_clearinghouse.py",
                "tests/integration/test_perp_engine_runtime_gate.py",
                "tests/integration/test_perp_engine_signed_surface_guards.py",
                "tests/integration/test_perp_op_auth_message_parity.py",
                "tests/integration/test_perps_api.py",
            ),
        ),
    },
    {
        "axis_id": "tau_witness_autotrader_binding_surface",
        "priority_score": -23,
        "surface_ids": (
            "api_request_authorization_boundary",
            "operations_signature_reuse_boundary",
            "settlement_attestation_policy_boundary",
        ),
        "what_if": "Autotrader Tau witnesses for budget, compile, execution, source registry, live admission, nonce, observation, session, signal, submit, wallet, and confidential extension bind different roots.",
        "disaster_state_template": "Tau witness-valid autotrader bundle authorizes a stale or cross-context action",
        "mutation_families": (
            "submit bundle witness reuses a stale observation packet root",
            "wallet capability guard passes while session binding belongs to a neighboring policy",
            "confidential extension live admission changes after Tau witness construction",
        ),
        "bounded_harness_ideas": (
            "run Tau autotrader witness modules as one binding-surface lane",
            "reject every witness bundle whose policy, nonce, source, session, wallet, and confidential roots are not identical",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/integration/test_tau_witness_autotrader_budget_guard.py",
                "tests/integration/test_tau_witness_autotrader_compilation_witness.py",
                "tests/integration/test_tau_witness_autotrader_compile_contract.py",
                "tests/integration/test_tau_witness_autotrader_emit_finalize.py",
                "tests/integration/test_tau_witness_autotrader_execution_guard.py",
                "tests/integration/test_tau_witness_autotrader_external_signal_source_registry_guard.py",
                "tests/integration/test_tau_witness_autotrader_live_admission_bundle.py",
                "tests/integration/test_tau_witness_autotrader_nonce_guard.py",
                "tests/integration/test_tau_witness_autotrader_observation_packet_contract.py",
                "tests/integration/test_tau_witness_autotrader_oracle_freshness_guard.py",
                "tests/integration/test_tau_witness_autotrader_session_capability_binding_guard.py",
                "tests/integration/test_tau_witness_autotrader_session_state_guard.py",
                "tests/integration/test_tau_witness_autotrader_signal_provenance_guard.py",
                "tests/integration/test_tau_witness_autotrader_submit_bundle_guard.py",
                "tests/integration/test_tau_witness_autotrader_system_compose.py",
                "tests/integration/test_tau_witness_autotrader_tx_envelope_guard.py",
                "tests/integration/test_tau_witness_autotrader_wallet_capability_guard.py",
                "tests/integration/test_tau_witness_autotrader_wallet_outbound_guard.py",
                "tests/integration/test_tau_witness_confidential_extension_live_admission.py",
            ),
        ),
    },
    {
        "axis_id": "fire_registry_deployment_sync_boundary",
        "priority_score": -24,
        "surface_ids": (
            "settlement_attestation_policy_boundary",
            "stale_settlement_boundary",
            "quote_receipt_certificate_boundary",
        ),
        "what_if": "FIRE registry deployment contracts, receipts, index, snapshots, settlement apply artifacts, and source-tree sync checks validate under different registry roots.",
        "disaster_state_template": "registry-deployed FIRE artifact replays against stale source or snapshot roots",
        "mutation_families": (
            "deployment receipt uses a registry index from a neighboring snapshot",
            "settlement apply artifact remains valid after source-tree sync root changes",
            "published registry snapshot omits a proof artifact required by the deployment contract",
        ),
        "bounded_harness_ideas": (
            "compose FIRE registry deployment, index, snapshot, settlement apply, publish, and sync CLIs",
            "fail closed unless every registry, source-tree, and settlement apply root agrees",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/integration/test_fire_registry_deployment_contract_cli.py",
                "tests/integration/test_fire_registry_deployment_receipt_cli.py",
                "tests/integration/test_fire_registry_index_cli.py",
                "tests/integration/test_fire_registry_snapshot.py",
                "tests/integration/test_fire_settlement_apply_artifact_receipt_cli.py",
                "tests/integration/test_publish_fire_registry_snapshot_cli.py",
                "tests/integration/test_sync_fire_source_tree_cli.py",
            ),
        ),
    },
    {
        "axis_id": "tla_queue_lifecycle_model_boundary",
        "priority_score": -25,
        "surface_ids": (
            "route_canonicalization_boundary",
            "stale_settlement_boundary",
            "settlement_attestation_policy_boundary",
        ),
        "what_if": "TLA queue, reorg, fee-priority, oracle-recovery, perps-scheduler, and settlement-witness lifecycle models permit a sequence that the runtime harnesses do not jointly name.",
        "disaster_state_template": "model-valid queue or lifecycle sequence hides stale route, oracle, or settlement replay",
        "mutation_families": (
            "exact-out adaptive queue accepts after reorg and fee-priority reorder",
            "oracle recovery lifecycle races perps scheduler epoch advance",
            "settlement witness lifecycle model permits stale witness after queue drain",
        ),
        "bounded_harness_ideas": (
            "run TLA queue and lifecycle models as a cross-surface scenario generator",
            "promote every model survivor into a concrete runtime sequence or keep it as inconclusive backlog",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/formal/test_tla_exact_out_adaptive_builder_competition.py",
                "tests/formal/test_tla_exact_out_adaptive_builder_reorg_queue.py",
                "tests/formal/test_tla_exact_out_adaptive_fee_priority_queue.py",
                "tests/formal/test_tla_exact_out_adaptive_fee_priority_reorg_queue.py",
                "tests/formal/test_tla_exact_out_adaptive_ingress_queue.py",
                "tests/formal/test_tla_exact_out_adaptive_liveness.py",
                "tests/formal/test_tla_exact_out_adaptive_single_reorg_queue.py",
                "tests/formal/test_tla_oracle_recovery_lifecycle.py",
                "tests/formal/test_tla_perp_epoch_scheduler.py",
                "tests/formal/test_tla_settlement_witness_lifecycle.py",
            ),
        ),
    },
    {
        "axis_id": "exact_out_shadow_runtime_prefilter_boundary",
        "priority_score": -26,
        "surface_ids": (
            "route_canonicalization_boundary",
            "quote_receipt_certificate_boundary",
            "api_request_authorization_boundary",
        ),
        "what_if": "Exact-out differential-discovery shadow adapters, runtime checkers, and prefilter corpus witnesses agree locally while long adaptive liveness benchmarks still expose expensive unexplored backlog.",
        "disaster_state_template": "shadow/runtime-valid exact-out quote omits a prefilter or runtime-canonical candidate",
        "mutation_families": (
            "DD shadow output certifies a route the runtime checker rejects",
            "prefilter corpus support witness drops a feasible canonical winner",
            "adaptive liveness benchmark exceeds bounded disaster-runner budget and remains backlog",
        ),
        "bounded_harness_ideas": (
            "promote the fast shadow/runtime and prefilter corpus lanes into the official receipt",
            "keep the 11-minute adaptive liveness and repaired-replacement benchmarks outside bounded unreachable claims",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/integration/test_exact_out_dd_shadow_adapter.py",
                "tests/integration/test_exact_out_dd_shadow_cli.py",
                "tests/integration/test_exact_out_runtime_checker.py",
            ),
            (
                "pytest",
                "-q",
                "tests/core/test_exact_out_many_pool_prefilter_corpus_benchmark_v1.py",
            ),
        ),
    },
    {
        "axis_id": "tau_runner_subprocess_transport_boundary",
        "priority_score": -27,
        "surface_ids": (
            "api_request_authorization_boundary",
            "settlement_attestation_policy_boundary",
            "operations_signature_reuse_boundary",
        ),
        "what_if": "Tau subprocess execution accepts a prompt, IO mode, or transport wrapper that the broader Tau runner utility suite can only cover conditionally when external binaries are present.",
        "disaster_state_template": "subprocess-valid Tau execution degrades into optimistic policy or settlement admission",
        "mutation_families": (
            "Tau subprocess returns malformed output that wrapper treats as policy success",
            "prompt or input mode changes while runner status remains successful",
            "external-binary skipped coverage is mistaken for unreachable transport states",
        ),
        "bounded_harness_ideas": (
            "promote only the no-skip Tau subprocess lane into bounded receipts",
            "keep broader Tau runner suites with skipped external-binary cases as explicit inconclusive backlog",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/integration/test_tau_runner_subprocess.py",
            ),
        ),
    },
    {
        "axis_id": "settlement_apply_witness_native_boundary",
        "priority_score": -28,
        "surface_ids": (
            "stale_settlement_boundary",
            "settlement_attestation_policy_boundary",
            "quote_receipt_certificate_boundary",
        ),
        "what_if": "Settlement runtime, create-pool, add/remove-liquidity, swap, exact-out swap, and ratio witnesses validate different apply semantics at ML-BVA boundaries.",
        "disaster_state_template": "native settlement witness-valid operation applies different pool or balance semantics than runtime settlement",
        "mutation_families": (
            "create-pool witness accepted while runtime settlement rejects the same state shape",
            "add/remove liquidity ratio witness drifts from apply witness under boundary reserves",
            "exact-out swap ML-BVA case changes the native apply result without changing receipt shape",
        ),
        "bounded_harness_ideas": (
            "compose runtime settlement tests with settlement native adapters and ML-BVA replay artifacts",
            "reject every settlement witness whose native apply result cannot be replayed by the runtime semantics",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/core/test_settlement.py",
                "tests/core/test_settlement_swap_runtime_v1.py",
                "tests/kernels/test_settlement_create_pool_apply_witness_v1_native_adapter.py",
                "tests/kernels/test_settlement_add_liquidity_apply_witness_v1_native_adapter.py",
                "tests/kernels/test_settlement_add_liquidity_ratio_witness_v1_native_adapter.py",
                "tests/kernels/test_settlement_remove_liquidity_apply_witness_v1_native_adapter.py",
                "tests/kernels/test_settlement_swap_apply_witness_v1_ml_bva_cases.py",
                "tests/kernels/test_settlement_swap_exact_out_apply_witness_v1_ml_bva_cases.py",
            ),
        ),
    },
    {
        "axis_id": "tau_operator_policy_receipt_symbolic_boundary",
        "priority_score": -29,
        "surface_ids": (
            "api_request_authorization_boundary",
            "operations_signature_reuse_boundary",
            "settlement_attestation_policy_boundary",
        ),
        "what_if": "Tau operator policy boundary, deployment, evidence, lowering, PCC, signed-bundle checks, symbolic aliases, and user policy validate incompatible policy roots.",
        "disaster_state_template": "receipt-valid Tau operator policy authorizes under a stale symbolic alias or user-policy root",
        "mutation_families": (
            "boundary receipt passes after signed bundle root changes",
            "symbolic policy alias metadata chain points to a neighboring lowered artifact",
            "user policy accepts an operator surface whose evidence bundle receipt is stale",
        ),
        "bounded_harness_ideas": (
            "compose operator receipt checkers with symbolic policy and user policy tests",
            "fail closed unless every operator policy receipt binds the same deployment, evidence, lowering, PCC, signature, and user-policy root",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/integration/test_check_tau_operator_policy_boundary_receipt.py",
                "tests/integration/test_check_tau_operator_policy_deployment_receipt.py",
                "tests/integration/test_check_tau_operator_policy_evidence_bundle.py",
                "tests/integration/test_check_tau_operator_policy_lowering_receipt.py",
                "tests/integration/test_check_tau_operator_policy_pcc_obligation.py",
                "tests/integration/test_check_tau_operator_policy_signed_bundle.py",
                "tests/integration/test_tau_operator_policy_surface.py",
                "tests/integration/test_tau_symbolic_operator_policy.py",
                "tests/integration/test_tau_symbolic_policy_alias_metadata_chain.py",
                "tests/integration/test_tau_user_policy.py",
            ),
        ),
    },
    {
        "axis_id": "settlement_price_provenance_semantic_boundary",
        "priority_score": -30,
        "surface_ids": (
            "settlement_attestation_policy_boundary",
            "stale_settlement_boundary",
            "route_canonicalization_boundary",
        ),
        "what_if": "Settlement price attestation, provenance, stability, aligned rails, accounting semantics, compact-bundle refinement, and replay certificates bind different price histories.",
        "disaster_state_template": "price-provenance-valid settlement packet realizes PnL under a neighboring price history",
        "mutation_families": (
            "price provenance root changes after attestation but before compact-bundle replay",
            "aligned rails accept a price history whose accounting semantic lane rejects",
            "settlement certificate replay uses a stale price stability witness",
        ),
        "bounded_harness_ideas": (
            "run price attestation, provenance, Tau stability, rails, accounting, refinement, and replay checks together",
            "reject settlement unless the price history root is identical across attestation, Tau rails, accounting, and replay certificates",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/integration/test_settlement_price_attestation.py",
                "tests/integration/test_settlement_price_provenance.py",
                "tests/tau/test_settlement_price_stability.py",
                "tests/tau/test_settlement_price_rails_aligned.py",
                "tests/tau/test_settlement_accounting_semantic_lane.py",
                "tests/tau/test_settlement_compact_bundle_refinement.py",
                "tests/tau/test_settlement_certificate_replay_compact_bundle.py",
            ),
        ),
    },
    {
        "axis_id": "fire_kernel_release_verifier_boundary",
        "priority_score": -31,
        "surface_ids": (
            "settlement_attestation_policy_boundary",
            "stale_settlement_boundary",
            "quote_receipt_certificate_boundary",
        ),
        "what_if": "FIRE kernel acceptance/apply receipts, compiler/interface registries, instances, locks, manifests, persisted bundles, releases, verifier receipts, rules, and ZPL artifacts validate different release roots.",
        "disaster_state_template": "release-valid FIRE kernel artifact verifies under a stale compiler, manifest, or persisted settlement bundle",
        "mutation_families": (
            "verifier receipt binds a release root whose compiler registry changed",
            "persisted bundle settlement replays after FIRE manifest or lock drift",
            "ZPL artifact passes verifier rules while native settlement adapter binds a neighboring release",
        ),
        "bounded_harness_ideas": (
            "compose FIRE kernel receipts, registries, object compiler/package, releases, persisted bundles, source verifier, and ZPL tests",
            "fail closed unless compiler, interface, manifest, release, verifier, and persisted settlement roots agree",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/kernels/test_fire_acceptance_receipt_v1.py",
                "tests/kernels/test_fire_apply_receipt_v1.py",
                "tests/kernels/test_fire_compiler_registry_v1.py",
                "tests/kernels/test_fire_instance_v1.py",
                "tests/kernels/test_fire_interface_registry_v1.py",
                "tests/kernels/test_fire_kernel_settlement_v1.py",
                "tests/kernels/test_fire_ledger_adapter_v1.py",
                "tests/kernels/test_fire_lock_v1.py",
                "tests/kernels/test_fire_manifest_v1.py",
                "tests/kernels/test_fire_native_adapter_settlement_v1.py",
                "tests/kernels/test_fire_object_compiler_v1.py",
                "tests/kernels/test_fire_object_package_v1.py",
                "tests/kernels/test_fire_persisted_bundle_settlement_v1.py",
                "tests/kernels/test_fire_registry_deployment_contract_v1.py",
                "tests/kernels/test_fire_registry_release_v1.py",
                "tests/kernels/test_fire_release_assurance.py",
                "tests/kernels/test_fire_settlement_apply_artifact_v1.py",
                "tests/kernels/test_fire_settlement_apply_report_v1.py",
                "tests/kernels/test_fire_src_settlement_verifier_v1.py",
                "tests/kernels/test_fire_verifier_receipt_v1.py",
                "tests/kernels/test_fire_verifier_rules_spec.py",
                "tests/kernels/test_fire_zpl_v1.py",
            ),
        ),
    },
    {
        "axis_id": "quote_receipt_native_adapter_parity_boundary",
        "priority_score": -32,
        "surface_ids": (
            "quote_receipt_transport_boundary",
            "quote_receipt_certificate_boundary",
            "stale_quote_receipt_boundary",
        ),
        "what_if": "Quote receipt native adapters for precheck, certificate, hop replay, hop structure, leg summary, pool snapshot, and totals agree locally but disagree with the composed receipt language.",
        "disaster_state_template": "native-adapter-valid quote receipt passes a decomposed gate but fails composed receipt replay",
        "mutation_families": (
            "native precheck accepts while certificate gate rejects after body repair",
            "hop replay and leg summary bind different route hashes",
            "pool snapshot gate accepts a stale pool root while totals gate remains valid",
        ),
        "bounded_harness_ideas": (
            "run quote receipt native adapters as the adapter-parity complement to core receipt decomposition tests",
            "reject every receipt unless native precheck, certificate, hop, leg, pool, and totals gates bind the same canonical envelope",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/kernels/test_quote_receipt_certificate_gate_v1_native_adapter.py",
                "tests/kernels/test_quote_receipt_hop_replay_gate_v1_native_adapter.py",
                "tests/kernels/test_quote_receipt_hop_structure_gate_v1_native_adapter.py",
                "tests/kernels/test_quote_receipt_leg_summary_gate_v1_native_adapter.py",
                "tests/kernels/test_quote_receipt_pool_snapshot_gate_v1_native_adapter.py",
                "tests/kernels/test_quote_receipt_precheck_gate_v1_native_adapter.py",
                "tests/kernels/test_quote_receipt_totals_gate_v1_native_adapter.py",
            ),
        ),
    },
    {
        "axis_id": "perp_native_adapter_oracle_bva_boundary",
        "priority_score": -33,
        "surface_ids": (
            "settlement_attestation_policy_boundary",
            "stale_settlement_boundary",
            "api_request_authorization_boundary",
        ),
        "what_if": "Perps native adapters and ML-BVA artifacts drift from the hardened oracle-settlement rule at funding, liquidation, signed-surface, runtime-risk, and ingress boundaries.",
        "disaster_state_template": "native perps adapter-valid transition settles or liquidates under missing oracle state",
        "mutation_families": (
            "ML-BVA settle_epoch case expects success without oracle_seen and positive index price",
            "funding witness accepts after oracle freshness and runtime risk gates disagree",
            "signed surface native adapter admits a market-version edge rejected by Tau ingress",
        ),
        "bounded_harness_ideas": (
            "run perps native adapters with the ML-BVA artifact that previously contained stale missing-oracle settlement expectations",
            "fail closed unless native adapters, generated BVA cases, and perps core guards agree on usable oracle requirements",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/kernels/test_perp_apply_funding_auto_gate_v1_native_adapter.py",
                "tests/kernels/test_perp_clearinghouse_market_params_guard_v1_native_adapter.py",
                "tests/kernels/test_perp_epoch_isolated_v3_ml_bva_cases.py",
                "tests/kernels/test_perp_funding_apply_v1_native_adapter.py",
                "tests/kernels/test_perp_liquidation_eligibility_v1_native_adapter.py",
                "tests/kernels/test_perp_market_version_prefix_guard_v1_native_adapter.py",
                "tests/kernels/test_perp_runtime_risk_gate_v1_native_adapter.py",
                "tests/kernels/test_perp_signed_surface_guard_v1_native_adapter.py",
                "tests/kernels/test_perp_submission_auth_field_selector_gate_v1_native_adapter.py",
                "tests/kernels/test_perp_submission_auth_gate_v1_native_adapter.py",
                "tests/kernels/test_perp_tau_ingress_stream_v1_native_adapter.py",
                "tests/kernels/test_funding_rate_settlement_witness_v1_1_native_adapter.py",
            ),
        ),
    },
    {
        "axis_id": "intent_nonce_confidential_state_native_boundary",
        "priority_score": -34,
        "surface_ids": (
            "nonce_replay_guard",
            "api_request_authorization_boundary",
            "quote_receipt_transport_boundary",
        ),
        "what_if": "Intent nonce native adapters, confidential request state, and volatility state agree locally but compose into a replayable confidential or volatile-state request.",
        "disaster_state_template": "nonce-native-valid state transition replays a confidential request or stale volatility observation",
        "mutation_families": (
            "nonce batch policy accepts after confidential request root drift",
            "sender resolution native adapter binds a neighboring confidential state object",
            "volatility state update changes after nonce sequence witness construction",
        ),
        "bounded_harness_ideas": (
            "compose intent nonce native adapters with confidential request and volatility state tests",
            "reject every state request whose nonce domain, confidential root, and volatility observation root do not agree",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/kernels/test_intent_nonce_batch_policy_gate_v1_native_adapter.py",
                "tests/kernels/test_intent_nonce_sender_resolution_gate_v1_native_adapter.py",
                "tests/kernels/test_intent_nonce_sequence_gate_v1_native_adapter.py",
                "tests/state/test_confidential_requests.py",
                "tests/state/test_volatility.py",
            ),
        ),
    },
    {
        "axis_id": "tla_perp_settlement_queue_model_boundary",
        "priority_score": -35,
        "surface_ids": (
            "settlement_attestation_policy_boundary",
            "stale_settlement_boundary",
            "api_request_authorization_boundary",
        ),
        "what_if": "Perps liquidation/submission queues and settlement witness queues permit reorg, fee-priority, builder-competition, or open-ingress schedules that runtime tests do not explicitly name.",
        "disaster_state_template": "TLA queue-valid schedule reaches stale perps or settlement witness admission after reorg",
        "mutation_families": (
            "perps liquidation queue drains after builder reorg with stale risk state",
            "perps submission fee-priority reorder changes market-version admissibility",
            "settlement witness inclusion queue accepts after bounded-open ingress drift",
        ),
        "bounded_harness_ideas": (
            "run perps liquidation/submission and settlement witness TLA queue models as a schedule-search lane",
            "promote every model survivor into a concrete runtime sequence before making stronger claims",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/formal/test_tla_perp_liquidation_bounded_open_ingress.py",
                "tests/formal/test_tla_perp_liquidation_builder_reorg_queue.py",
                "tests/formal/test_tla_perp_liquidation_queue_drain.py",
                "tests/formal/test_tla_perp_submission_builder_competition.py",
                "tests/formal/test_tla_perp_submission_builder_reorg_queue.py",
                "tests/formal/test_tla_perp_submission_fee_priority_queue.py",
                "tests/formal/test_tla_perp_submission_ingress_queue.py",
                "tests/formal/test_tla_perp_submission_single_reorg_queue.py",
                "tests/formal/test_tla_settlement_witness_bounded_open_ingress.py",
                "tests/formal/test_tla_settlement_witness_builder_competition.py",
                "tests/formal/test_tla_settlement_witness_builder_reorg_queue.py",
                "tests/formal/test_tla_settlement_witness_fee_priority_queue.py",
                "tests/formal/test_tla_settlement_witness_fee_priority_reorg_queue.py",
                "tests/formal/test_tla_settlement_witness_inclusion_queue.py",
                "tests/formal/test_tla_settlement_witness_single_reorg_queue.py",
            ),
        ),
    },
    {
        "axis_id": "exact_in_lean_rank_projection_boundary",
        "priority_score": -36,
        "surface_ids": (
            "route_canonicalization_boundary",
            "quote_receipt_certificate_boundary",
            "api_request_authorization_boundary",
        ),
        "what_if": "Exact-in Lean certificate, guarded quote, oracle contract, rank projection, packet, true-key interpretation, and winner proofs certify different route orders.",
        "disaster_state_template": "Lean-valid exact-in route certificate hides a noncanonical rank projection or true-key winner",
        "mutation_families": (
            "rank projection packet proves a candidate order that the true-key winner proof rejects",
            "oracle contract witness changes while guarded quote certificate remains valid",
            "exact-in certificate proof accepts a route outside the projected candidate domain",
        ),
        "bounded_harness_ideas": (
            "run exact-in Lean proofs and ESSO rank-projection packet checks together",
            "reject every exact-in certificate unless rank projection, guarded quote, oracle contract, true-key interpretation, and winner proof bind the same candidate order",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/formal/test_lean_exact_in_route_certificate.py",
                "tests/formal/test_lean_exact_in_route_guarded_quote_packet.py",
                "tests/formal/test_lean_exact_in_route_oracle_contract.py",
                "tests/formal/test_lean_exact_in_route_rank_projection.py",
                "tests/formal/test_lean_exact_in_route_rank_projection_packet.py",
                "tests/formal/test_lean_exact_in_route_true_key_interpretation_packet.py",
                "tests/formal/test_lean_exact_in_true_key_winner.py",
                "tests/formal/test_esso_exact_in_route_rank_projection_packet.py",
            ),
        ),
    },
    {
        "axis_id": "exact_out_lean_certificate_boundary",
        "priority_score": -37,
        "surface_ids": (
            "route_canonicalization_boundary",
            "quote_receipt_certificate_boundary",
            "api_request_authorization_boundary",
        ),
        "what_if": "Exact-out Lean brute-force completeness, canonical minimizer, many-pool domain, certified winner, guarded quote, oracle contract, and route certificate proofs bind different candidate sets.",
        "disaster_state_template": "Lean-valid exact-out certificate proves a winner outside the complete brute-force candidate domain",
        "mutation_families": (
            "canonical minimizer proof uses a candidate domain different from certified winner packet",
            "guarded quote packet proof accepts a route whose oracle contract proof rejects",
            "route certificate proof omits a brute-force-complete candidate",
        ),
        "bounded_harness_ideas": (
            "run exact-out Lean completeness and certificate proofs as one witness-language lane",
            "reject every exact-out certificate unless completeness, minimizer, domain, winner, guarded quote, oracle contract, and route certificate facts agree",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/formal/test_lean_exact_out_bruteforce_completeness.py",
                "tests/formal/test_lean_exact_out_canonical_minimizer.py",
                "tests/formal/test_lean_exact_out_many_pool_candidate_domain_contract.py",
                "tests/formal/test_lean_exact_out_many_pool_certified_winner_packet.py",
                "tests/formal/test_lean_exact_out_many_pool_guarded_quote_packet.py",
                "tests/formal/test_lean_exact_out_many_pool_oracle_contract.py",
                "tests/formal/test_lean_exact_out_route_certificate.py",
            ),
        ),
    },
    {
        "axis_id": "settlement_lean_price_oracle_boundary",
        "priority_score": -38,
        "surface_ids": (
            "settlement_attestation_policy_boundary",
            "stale_settlement_boundary",
            "quote_receipt_certificate_boundary",
        ),
        "what_if": "Settlement Lean compact bundle, end-to-end packet, LP/value packets, feature extension, price history, oracle benefit, and perps funding epoch proofs validate neighboring time or price roots.",
        "disaster_state_template": "Lean-valid settlement or oracle packet realizes value under a stale price/funding epoch",
        "mutation_families": (
            "price history certificate changes after compact bundle proof",
            "oracle benefit accounting proof binds a different risk class than settlement value packet",
            "perps funding epoch proof accepts a time root rejected by settlement packet proof",
        ),
        "bounded_harness_ideas": (
            "compose settlement/oracle Lean proofs into one price-time witness-language lane",
            "reject settlement promotion unless compact bundle, value packets, feature extension, price history, oracle benefit, and funding epoch proofs bind the same time root",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/formal/test_lean_settlement_compact_bundle.py",
                "tests/formal/test_lean_settlement_end_to_end_certificate_packet.py",
                "tests/formal/test_lean_settlement_endogenous_lp_value_packet.py",
                "tests/formal/test_lean_settlement_feature_extension_packet.py",
                "tests/formal/test_lean_settlement_price_history_certificate.py",
                "tests/formal/test_lean_settlement_value_packet.py",
                "tests/formal/test_lean_oracle_benefit_accounting.py",
                "tests/formal/test_lean_oracle_benefit_risk_classes.py",
                "tests/formal/test_lean_perp_funding_epoch_gate_proved.py",
            ),
        ),
    },
    {
        "axis_id": "ltl_oracle_recovery_schedule_boundary",
        "priority_score": -39,
        "surface_ids": (
            "settlement_attestation_policy_boundary",
            "stale_settlement_boundary",
            "api_request_authorization_boundary",
        ),
        "what_if": "Batch clearing, oracle recovery, perps scheduler, zUSD oracle recovery, Tau zUSD recovery, and API oracle contracts permit incompatible recovery schedules.",
        "disaster_state_template": "temporal-model-valid recovery schedule applies stale zUSD, perps, or batch state",
        "mutation_families": (
            "oracle recovery LTL permits a schedule rejected by zUSD Tau recovery",
            "perps scheduler advances while zUSD oracle contract remains in recovery mode",
            "batch clearing LTL accepts a recovery schedule whose API oracle contract root is stale",
        ),
        "bounded_harness_ideas": (
            "run LTL, ESSO, Tau, and API oracle recovery artifacts together",
            "reject recovery-mode promotion unless temporal model, Tau gate, zUSD contract, and API oracle roots agree",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/formal/test_batch_clearing_ltlf.py",
                "tests/formal/test_oracle_recovery_ltlf.py",
                "tests/formal/test_perp_epoch_scheduler_ltlf.py",
                "tests/formal/test_zusd_oracle_recovery_lifecycle_v1.py",
                "tests/formal/test_esso_zusd_oracle_recovery_lifecycle_v1.py",
                "tests/tau/test_tau_zusd_oracle_recovery_lifecycle.py",
                "tests/integration/test_zusd_oracle_contracts.py",
                "tests/integration/test_zusd_tau_gate_edges.py",
            ),
        ),
    },
    {
        "axis_id": "exact_out_lean_concrete_recursion_boundary",
        "priority_score": -40,
        "surface_ids": (
            "route_canonicalization_boundary",
            "quote_receipt_certificate_boundary",
            "api_request_authorization_boundary",
        ),
        "what_if": "Exact-out concrete recursion, key-cover witness, runtime generator, and structural reachability proofs validate different recursive candidate decompositions.",
        "disaster_state_template": "Lean-valid exact-out recursion proof emits a candidate outside the runtime generator domain",
        "mutation_families": (
            "concrete recursion branch proof accepts a key-cover witness from a neighboring domain",
            "runtime generator checker emits a path whose structural recursion proof rejects",
            "key-cover bridge proves coverage after recursive depth accounting drift",
        ),
        "bounded_harness_ideas": (
            "run concrete recursion, key-cover, runtime generator, and structural reachability Lean tests together",
            "reject every recursive exact-out witness unless generator, key cover, and structural reachability bind the same candidate tree",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/formal/test_lean_exact_out_many_pool_concrete_key_cover_witness.py",
                "tests/formal/test_lean_exact_out_many_pool_concrete_recursion_branch.py",
                "tests/formal/test_lean_exact_out_many_pool_concrete_recursion_reduction.py",
                "tests/formal/test_lean_exact_out_many_pool_key_cover_bridge.py",
                "tests/formal/test_lean_exact_out_many_pool_runtime_generator_checker.py",
                "tests/formal/test_lean_exact_out_many_pool_structural_recursion_reachability.py",
            ),
        ),
    },
    {
        "axis_id": "exact_out_lean_ordered_presentation_boundary",
        "priority_score": -41,
        "surface_ids": (
            "route_canonicalization_boundary",
            "quote_receipt_certificate_boundary",
            "api_request_authorization_boundary",
        ),
        "what_if": "Ordered path witness ladders, ordered quoted candidates, presentation bridges, and canonical-candidate minimum proofs agree locally but encode different path orderings.",
        "disaster_state_template": "ordered-presentation-valid exact-out proof hides a noncanonical path witness",
        "mutation_families": (
            "ordered quoted candidate bridge accepts a path outside the witness-shape ladder",
            "quoted presentation bridge changes path order while canonical minimum proof remains valid",
            "ordered quoted path completeness misses a presentation-equivalent candidate",
        ),
        "bounded_harness_ideas": (
            "compose ordered path, quoted candidate, presentation, realization, and canonical-minimum Lean proofs",
            "reject every ordered exact-out presentation unless witness shape, quoted path, presentation, and canonical minimum facts agree",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/formal/test_lean_exact_out_many_pool_ordered_path_witness_shape_ladder.py",
                "tests/formal/test_lean_exact_out_many_pool_ordered_quoted_candidate_bridge.py",
                "tests/formal/test_lean_exact_out_many_pool_ordered_quoted_path_completeness.py",
                "tests/formal/test_lean_exact_out_many_pool_ordered_quoted_presentation_bridge.py",
                "tests/formal/test_lean_exact_out_many_pool_path_witness_canonical_candidate_minimum.py",
                "tests/formal/test_lean_exact_out_many_pool_quoted_path_realization.py",
                "tests/formal/test_lean_exact_out_many_pool_quoted_presentation_bridge.py",
                "tests/formal/test_lean_exact_out_many_pool_quoted_structural_reachability.py",
            ),
        ),
    },
    {
        "axis_id": "exact_out_lean_repaired_key_cover_boundary",
        "priority_score": -42,
        "surface_ids": (
            "route_canonicalization_boundary",
            "quote_receipt_certificate_boundary",
            "api_request_authorization_boundary",
        ),
        "what_if": "Repaired exact-out advisory, full-domain certification, key-cover interpretation, semantic bridges, prefilter contracts, and witness extraction repair different candidate domains.",
        "disaster_state_template": "repaired exact-out proof certifies a winner after key-cover or prefilter semantic drift",
        "mutation_families": (
            "repaired key-cover packet validates while semantic bridge binds a neighboring interpretation",
            "repaired prefilter contract drops a candidate restored by full-domain certification",
            "witness extraction proves a repaired advisory quote outside key-cover semantics",
        ),
        "bounded_harness_ideas": (
            "run repaired advisory, full-domain, key-cover, prefilter, semantic bridge, and witness-extraction Lean tests together",
            "reject repaired exact-out proofs unless all repair artifacts bind one candidate domain and one winner relation",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/formal/test_lean_exact_out_many_pool_prefilter_contract.py",
                "tests/formal/test_lean_exact_out_many_pool_prefilter_contraction_bridge.py",
                "tests/formal/test_lean_exact_out_many_pool_prefilter_support_bridge.py",
                "tests/formal/test_lean_exact_out_many_pool_repaired_advisory_quote_packet.py",
                "tests/formal/test_lean_exact_out_many_pool_repaired_full_domain_certified_packet.py",
                "tests/formal/test_lean_exact_out_many_pool_repaired_key_cover_interpretation_packet.py",
                "tests/formal/test_lean_exact_out_many_pool_repaired_key_cover_interpretation_semantic_bridge.py",
                "tests/formal/test_lean_exact_out_many_pool_repaired_key_cover_packet.py",
                "tests/formal/test_lean_exact_out_many_pool_repaired_key_cover_semantic_bridge.py",
                "tests/formal/test_lean_exact_out_many_pool_repaired_key_cover_witness_extraction.py",
                "tests/formal/test_lean_exact_out_many_pool_repaired_prefilter_contract.py",
                "tests/formal/test_lean_exact_out_many_pool_repaired_prefilter_semantic_bridge.py",
            ),
        ),
    },
    {
        "axis_id": "permissionless_proof_mining_tooling_boundary",
        "priority_score": -43,
        "surface_ids": (
            "api_request_authorization_boundary",
            "nonce_replay_guard",
            "operations_signature_reuse_boundary",
        ),
        "what_if": "Permissionless operator preflight, proof-mining manager packets, status, release manifests, round ledgers, solver claims, assurance CLI, and runtime claimability bind different rounds or operators.",
        "disaster_state_template": "permissionless proof-mining tooling pays or advertises a claim under a stale round/operator root",
        "mutation_families": (
            "release manifest updates after proof-mining manager packet construction",
            "round ledger accepts a solver claim whose claimability gate rejects",
            "operator preflight passes while assurance CLI binds a neighboring manager status",
        ),
        "bounded_harness_ideas": (
            "compose permissionless operator, proof-mining manager/status, release, round, solver, assurance, and recovery tests",
            "reject every permissionless claim unless operator, manager packet, status, round ledger, and solver roots agree",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/tools/test_permissionless_operator_preflight.py",
                "tests/tools/test_permissionless_proof_mining_manager_packet.py",
                "tests/tools/test_permissionless_proof_mining_status.py",
                "tests/tools/test_permissionless_release_manifest.py",
                "tests/tools/test_permissionless_round_ledger.py",
                "tests/tools/test_permissionless_solver_proof_mining_claim.py",
                "tests/integration/test_permissionless_assurance_cli.py",
                "tests/integration/test_proof_mining_claimability.py",
                "tests/integration/test_tau_testnet_dex_plugin_recovery.py",
            ),
        ),
    },
    {
        "axis_id": "claims_falsifier_inventory_boundary",
        "priority_score": -44,
        "surface_ids": (
            "settlement_attestation_policy_boundary",
            "route_canonicalization_boundary",
            "api_request_authorization_boundary",
        ),
        "what_if": "Claim falsifiers, claim registry, TLA claim inventory, and blast-radius reports disagree about which mathematical or mechanism claims remain refuted.",
        "disaster_state_template": "claim-inventory-valid assurance report promotes a falsified mechanism claim",
        "mutation_families": (
            "falsifier output changes while claims registry status remains promoted",
            "TLA claim inventory omits a refuted AMM or fee-law claim",
            "blast-radius report treats a falsified claim as outside the affected surface",
        ),
        "bounded_harness_ideas": (
            "run mechanism claim falsifiers, registry, TLA inventory, and blast-radius report together",
            "reject assurance promotion if any falsifier, registry, inventory, or blast-radius artifact disagrees on claim status",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/core/test_abelian_network_claim_falsifier.py",
                "tests/core/test_chaotic_fee_claim_falsifier.py",
                "tests/core/test_clifford_amm_claim_falsifier.py",
                "tests/core/test_entropy_ot_claim_falsifier.py",
                "tests/core/test_iprojection_claim_falsifier.py",
                "tests/test_claims_registry.py",
                "tests/formal/test_tla_claim_inventory.py",
                "tests/integration/test_zenodex_blast_radius_report.py",
            ),
        ),
    },
    {
        "axis_id": "tau_semantic_proof_gate_split_boundary",
        "priority_score": -45,
        "surface_ids": (
            "api_request_authorization_boundary",
            "settlement_attestation_policy_boundary",
            "operations_signature_reuse_boundary",
        ),
        "what_if": "Tau authorization, expiry, oracle freshness, replay, sealed-bid, proof-mining, settlement module, buyback, and witness-lifecycle gates validate different semantic roots.",
        "disaster_state_template": "Tau semantic-gate-valid action crosses authorization, replay, oracle, or settlement proof domains",
        "mutation_families": (
            "authorization semantic lane accepts after replay semantic root drift",
            "oracle freshness semantic lane disagrees with proof-mining reward gate",
            "settlement buyback proof gate validates against a neighboring module bundle split",
        ),
        "bounded_harness_ideas": (
            "split Tau semantic gate checks into subcommands below the receipt timeout",
            "reject Tau semantic promotion unless authorization, expiry, oracle, replay, sealed-bid, proof-mining, and settlement proof roots agree",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/tau/test_authorization_semantic_lane.py",
                "tests/tau/test_cancel_expiry_semantic_lane.py",
                "tests/tau/test_oracle_freshness_semantic_lane.py",
                "tests/tau/test_replay_semantic_lane.py",
                "tests/tau/test_fhe_sealed_bid_alpha_guard.py",
                "tests/tau/test_proof_mining_reward_gate.py",
            ),
            (
                "pytest",
                "-q",
                "tests/tau/test_settlement_module_bundle_split.py",
                "tests/tau/test_settlement_v1_proof_gate.py",
                "tests/tau/test_settlement_v2_buyback_proof_gate.py",
            ),
            (
                "pytest",
                "-q",
                "tests/tau/test_settlement_v3_buyback_floor_proof_gate.py",
                "tests/tau/test_tau_settlement_witness_lifecycle.py",
            ),
        ),
    },
    {
        "axis_id": "tau_autotrader_spec_guard_boundary",
        "priority_score": -46,
        "surface_ids": (
            "api_request_authorization_boundary",
            "operations_signature_reuse_boundary",
            "settlement_attestation_policy_boundary",
        ),
        "what_if": "Tau autotrader spec guards for budget, compile, execution, live admission, nonce, oracle freshness, route sanity, session, signal, submit, system, tx envelope, and wallet bind different automation contexts.",
        "disaster_state_template": "Tau autotrader spec-valid bundle authorizes a stale or cross-context automated action",
        "mutation_families": (
            "Tau route sanity guard accepts after budget or compile witness drift",
            "session capability guard validates while wallet outbound guard binds a neighboring policy",
            "tx envelope guard passes after live-admission or nonce root changes",
        ),
        "bounded_harness_ideas": (
            "run the no-skip Tau autotrader spec subset as a semantic complement to integration witness tests",
            "keep the observation packet spec-mode timeout outside unreachable claims until it has a deterministic no-skip lane",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/tau/test_autotrader_budget_guard.py",
                "tests/tau/test_autotrader_compilation_witness.py",
                "tests/tau/test_autotrader_compile_contract.py",
                "tests/tau/test_autotrader_emit_finalize.py",
                "tests/tau/test_autotrader_execution_guard.py",
                "tests/tau/test_autotrader_external_signal_source_registry_guard.py",
                "tests/tau/test_autotrader_live_admission_bundle.py",
                "tests/tau/test_autotrader_nonce_guard.py",
                "tests/tau/test_autotrader_oracle_freshness_guard.py",
                "tests/tau/test_autotrader_route_economic_sanity_guard.py",
                "tests/tau/test_autotrader_session_capability_binding_guard.py",
                "tests/tau/test_autotrader_session_state_guard.py",
                "tests/tau/test_autotrader_signal_provenance_guard.py",
                "tests/tau/test_autotrader_submit_bundle_guard.py",
                "tests/tau/test_autotrader_system_compose.py",
                "tests/tau/test_autotrader_tx_envelope_guard.py",
                "tests/tau/test_autotrader_wallet_capability_guard.py",
                "tests/tau/test_autotrader_wallet_outbound_guard.py",
            ),
        ),
    },
    {
        "axis_id": "fire_formal_runtime_note_boundary",
        "priority_score": -47,
        "surface_ids": (
            "settlement_attestation_policy_boundary",
            "stale_settlement_boundary",
            "quote_receipt_certificate_boundary",
        ),
        "what_if": "FIRE formal burn-boost, fee-note, LP-loss-cover specs, native adapters, and reference runtimes validate different note roots.",
        "disaster_state_template": "FIRE runtime-note-valid artifact applies a stale burn, fee, or LP-loss-cover semantic root",
        "mutation_families": (
            "burn-boost formal spec accepts while native adapter binds a neighboring runtime note",
            "fee-note reference result changes after formal packet construction",
            "LP-loss-cover native adapter validates a root rejected by the reference runtime",
        ),
        "bounded_harness_ideas": (
            "run FIRE formal note specs with native adapters and reference runtimes",
            "reject FIRE note promotion unless formal, native, and reference artifacts bind the same runtime note root",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/formal/test_esso_fire_burn_boost_call_v1.py",
                "tests/formal/test_esso_fire_fee_note_v1.py",
                "tests/formal/test_esso_fire_lp_loss_cover_v1.py",
                "tests/kernels/test_fire_burn_boost_call_v1_native_adapter.py",
                "tests/kernels/test_fire_burn_boost_call_v1_ref.py",
                "tests/kernels/test_fire_fee_note_v1_native_adapter.py",
                "tests/kernels/test_fire_fee_note_v1_ref.py",
                "tests/kernels/test_fire_lp_loss_cover_v1_native_adapter.py",
                "tests/kernels/test_fire_lp_loss_cover_v1_ref.py",
            ),
        ),
    },
    {
        "axis_id": "numeric_kernel_ml_history_boundary",
        "priority_score": -48,
        "surface_ids": (
            "route_canonicalization_boundary",
            "stale_settlement_boundary",
            "api_request_authorization_boundary",
        ),
        "what_if": "CPMM, LP mint, LP ratio, generated kernel history vars, and exotic generated refs pass individually but disagree about numeric boundary history or generated-reference semantics.",
        "disaster_state_template": "ML-BVA-valid numeric kernel artifact hides generated-reference or history-var drift",
        "mutation_families": (
            "CPMM ML-BVA case mutates a boundary ignored by generated history vars",
            "LP mint and LP ratio ML-BVA artifacts disagree on shared reserve boundaries",
            "exotic generated ref accepts a history-var transition rejected by kernel history tests",
        ),
        "bounded_harness_ideas": (
            "run numeric ML-BVA artifacts with generated kernel history and exotic refs",
            "reject numeric kernel promotion unless ML-BVA replay, history vars, and generated refs agree at boundary values",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/kernels/test_cpmm_swap_v8_ml_bva_cases.py",
                "tests/kernels/test_lp_mint_v8_ml_bva_cases.py",
                "tests/kernels/test_lp_ratio_calculator_v7_ml_bva_cases.py",
                "tests/kernels/test_lp_math_v7.py",
                "tests/core/test_generated_kernel_history_vars.py",
                "tests/exotic_state_machines/test_generated_exotic_refs.py",
            ),
        ),
    },
    {
        "axis_id": "proof_mining_native_permissionless_boundary",
        "priority_score": -49,
        "surface_ids": (
            "api_request_authorization_boundary",
            "nonce_replay_guard",
            "operations_signature_reuse_boundary",
        ),
        "what_if": "Proof-mining native claim gates, manager adapter, verification flags, permissionless manager packets, status, and solver claims bind different manager states.",
        "disaster_state_template": "native proof-mining manager-valid claim executes under stale permissionless manager state",
        "mutation_families": (
            "native manager adapter accepts a packet rejected by permissionless manager packet tooling",
            "verification flags gate passes while solver proof-mining claim uses a stale status root",
            "claim identity native gate binds a neighboring manager state",
        ),
        "bounded_harness_ideas": (
            "compose proof-mining native adapters with permissionless manager/status/solver tools",
            "reject proof-mining claims unless native gates and permissionless tooling bind the same manager state root",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/kernels/test_proof_mining_claim_gate_v1_native_adapter.py",
                "tests/kernels/test_proof_mining_claim_identity_gate_v1_native_adapter.py",
                "tests/kernels/test_proof_mining_manager_packet_envelope_gate_v1_native_adapter.py",
                "tests/kernels/test_proof_mining_manager_v1_adapter.py",
                "tests/kernels/test_proof_mining_manager_verification_flags_gate_v1_native_adapter.py",
                "tests/tools/test_permissionless_proof_mining_manager_packet.py",
                "tests/tools/test_permissionless_proof_mining_status.py",
                "tests/tools/test_permissionless_solver_proof_mining_claim.py",
            ),
        ),
    },
    {
        "axis_id": "exact_out_lean_stream_support_boundary",
        "priority_score": -50,
        "surface_ids": (
            "route_canonicalization_boundary",
            "quote_receipt_certificate_boundary",
            "api_request_authorization_boundary",
        ),
        "what_if": "CPMM quote totality, ordered quoted path completeness, quote streams, witness streams, selected domains, residual allocation, remaining capacity, and support presentations validate different exact-out stream languages.",
        "disaster_state_template": "stream-valid exact-out witness omits a supported residual allocation or capacity candidate",
        "mutation_families": (
            "quote stream completeness misses a candidate present in selected-domain emission",
            "remaining capacity top-sum proof disagrees with residual allocation proof",
            "support presentation validates while witness stream binds a neighboring quoted path",
        ),
        "bounded_harness_ideas": (
            "split exact-out Lean stream/support proofs into two under-timeout commands",
            "reject exact-out stream witnesses unless quote totality, streams, selected domains, residual allocation, capacity, and support facts agree",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/formal/test_lean_exact_out_many_pool_cpmm_ordered_quoted_path_completeness.py",
                "tests/formal/test_lean_exact_out_many_pool_cpmm_quote_totality.py",
                "tests/formal/test_lean_exact_out_many_pool_cpmm_quoted_path_quote_stream_completeness.py",
                "tests/formal/test_lean_exact_out_many_pool_quoted_path_quote_stream_completeness.py",
                "tests/formal/test_lean_exact_out_many_pool_quoted_path_stream_bridge.py",
                "tests/formal/test_lean_exact_out_many_pool_quoted_witness_stream_bridge.py",
            ),
            (
                "pytest",
                "-q",
                "tests/formal/test_lean_exact_out_many_pool_reindexed_residual_allocation.py",
                "tests/formal/test_lean_exact_out_many_pool_remaining_capacity_envelope.py",
                "tests/formal/test_lean_exact_out_many_pool_remaining_capacity_top_sum.py",
                "tests/formal/test_lean_exact_out_many_pool_residual_allocation.py",
                "tests/formal/test_lean_exact_out_many_pool_selected_domain_certified_bridge.py",
                "tests/formal/test_lean_exact_out_many_pool_selected_domain_completeness.py",
                "tests/formal/test_lean_exact_out_many_pool_selected_domain_emission_bridge.py",
                "tests/formal/test_lean_exact_out_many_pool_support_head_bounds.py",
                "tests/formal/test_lean_exact_out_many_pool_support_presentation.py",
                "tests/formal/test_lean_exact_out_many_pool_support_tail_recursion.py",
            ),
        ),
    },
    {
        "axis_id": "cross_module_tool_checker_boundary",
        "priority_score": -51,
        "surface_ids": (
            "settlement_attestation_policy_boundary",
            "route_canonicalization_boundary",
            "api_request_authorization_boundary",
        ),
        "what_if": "Cross-module oracle, curve registry, exact-out generator gap, oracle divergence, perps risk envelope, settlement compact-bundle scope, Tau runtime subset, and GPU route witness checkers disagree.",
        "disaster_state_template": "tool-checker-valid release hides a cross-module oracle, curve, risk, or generator-gap disagreement",
        "mutation_families": (
            "oracle split-brain checker passes while oracle divergence pack flags a neighboring root",
            "exact-out generator gap checker accepts a candidate rejected by GPU route witness tooling",
            "perps risk envelope checker passes while Tau runtime subset excludes the required gate",
        ),
        "bounded_harness_ideas": (
            "run cross-module checker tools as an assurance-layer consistency lane",
            "reject release promotion if any checker disagrees on oracle, curve, exact-out, perps, settlement, Tau subset, or GPU witness roots",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/tools/test_check_cross_module_oracle_split_brain_v1.py",
                "tests/tools/test_check_curve_registry_fail_closed_v1.py",
                "tests/tools/test_check_exact_out_many_pool_generator_gap_v1.py",
                "tests/tools/test_check_oracle_divergence_pack_v1.py",
                "tests/tools/test_check_perp_risk_envelope_containment_v1.py",
                "tests/tools/test_check_settlement_compact_bundle_scope_gap_v1.py",
                "tests/tools/test_check_tau_supported_runtime_subset.py",
                "tests/tools/test_gpu_argminmax_certificate_tau_verify.py",
                "tests/tools/test_gpu_route_improvement_witness.py",
            ),
        ),
    },
    {
        "axis_id": "stateful_report_bridge_ranking_boundary",
        "priority_score": -52,
        "surface_ids": (
            "api_request_authorization_boundary",
            "route_canonicalization_boundary",
            "settlement_attestation_policy_boundary",
        ),
        "what_if": "RC1 candidate indexes, region BA bridge reports, stateful feedback, Zenograph ranking review indexes, promotion gates, and ZAG bridge KRR disagree about promoted scenario priority.",
        "disaster_state_template": "report-bridge-valid ranking promotes a stale or unsupported scenario candidate",
        "mutation_families": (
            "RC1 candidate index changes after stateful feedback report construction",
            "region BA report bridge promotes a candidate rejected by Zenograph ranking gate",
            "ZAG bridge KRR accepts a ranking review index with stale scenario evidence",
        ),
        "bounded_harness_ideas": (
            "compose candidate index, bridge, feedback, ranking review, promotion gate, and ZAG bridge tests",
            "reject report promotion unless candidate, region, stateful feedback, ranking, and KRR roots agree",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/integration/test_rc1_candidate_index.py",
                "tests/integration/test_region_ba_report_bridge.py",
                "tests/integration/test_stateful_feedback.py",
                "tests/integration/test_zenograph_autotrader_ranking_review_campaign_index_cli.py",
                "tests/kernels/test_zenograph_ranking_promotion_gate_v1_adapter.py",
                "tests/tools/test_zenodex_zag_bridge_krr.py",
            ),
        ),
    },
    {
        "axis_id": "tau_operator_library_artifact_boundary",
        "priority_score": -53,
        "surface_ids": (
            "api_request_authorization_boundary",
            "operations_signature_reuse_boundary",
            "settlement_attestation_policy_boundary",
        ),
        "what_if": "Lowered Tau operator artifacts, operator library bootstrap, typed manifests, RC1 runtime paths, and TLA claim summaries validate different operator-library roots.",
        "disaster_state_template": "operator-library-valid artifact executes under a stale lowered or typed-manifest root",
        "mutation_families": (
            "lowered operator policy artifact passes while typed operator manifest changes",
            "operator library bootstrap emits a root not rendered in RC1 supported runtime path",
            "TLA claim summary references a neighboring operator-library artifact",
        ),
        "bounded_harness_ideas": (
            "run lowered artifact, operator library, typed manifest, RC1 render, and TLA summary tests together",
            "reject operator library promotion unless lowered, bootstrap, manifest, runtime path, and TLA summary roots agree",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/integration/test_check_tau_lowered_operator_policy_artifact.py",
                "tests/integration/test_tau_lowered_operator_policy_artifact.py",
                "tests/integration/test_tau_operator_library.py",
                "tests/integration/test_bootstrap_typed_operator_library.py",
                "tests/integration/test_check_typed_operator_manifest.py",
                "tests/tools/test_render_rc1_supported_runtime_path.py",
                "tests/tools/test_render_tla_claim_summary.py",
            ),
        ),
    },
    {
        "axis_id": "tau_exact_out_resource_spec_boundary",
        "priority_score": -54,
        "surface_ids": (
            "route_canonicalization_boundary",
            "quote_receipt_certificate_boundary",
            "api_request_authorization_boundary",
        ),
        "what_if": "Tau exact-out adaptive/audited liveness, packet facts, perps specs, regret frontier, resource bridge, and zUSD specs validate neighboring runtime-resource assumptions.",
        "disaster_state_template": "Tau spec-valid route or resource witness executes outside audited liveness or runtime resource bounds",
        "mutation_families": (
            "exact-out packet facts pass while audited bounds liveness rejects the runtime path",
            "resource bridge Tau spec validates a route outside exact-out adaptive liveness",
            "perps or zUSD Tau spec changes resource assumptions after regret frontier construction",
        ),
        "bounded_harness_ideas": (
            "run Tau exact-out, audited bounds, packet facts, perps, regret frontier, resource bridge, and zUSD specs as one under-cap lane",
            "reject Tau resource promotion unless exact-out, resource, perps, regret, and zUSD specs share the same runtime-bound assumptions",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/tau/test_exact_out_many_pool_adaptive_liveness.py",
                "tests/tau/test_exact_out_many_pool_audited_bounds_liveness.py",
                "tests/tau/test_exact_out_packet_facts.py",
                "tests/tau/test_perps_tau_specs.py",
                "tests/tau/test_regret_frontier_tau_specs.py",
                "tests/tau/test_resource_bridge_tau_specs.py",
                "tests/tau/test_zusd_tau_specs.py",
            ),
        ),
    },
    {
        "axis_id": "dex_settlement_recovery_proof_unit_boundary",
        "priority_score": -55,
        "surface_ids": (
            "stale_settlement_boundary",
            "settlement_attestation_policy_boundary",
            "api_request_authorization_boundary",
        ),
        "what_if": "DEX settlement sequence grammar, proof-verifier unit checks, proof-mining claimability, and Tau Testnet recovery validate different recovered settlement or proof states.",
        "disaster_state_template": "recovery-valid DEX settlement or proof-mining state replays stale proof or claimability context",
        "mutation_families": (
            "settlement sequence grammar accepts after proof-verifier unit rejects proof context",
            "proof-mining claimability passes under a recovered Tau Testnet state with stale manager root",
            "recovery path rebuilds settlement state without matching proof-verifier unit root",
        ),
        "bounded_harness_ideas": (
            "compose DEX settlement sequence grammar, proof-verifier unit, proof-mining claimability, and Tau Testnet recovery tests",
            "reject recovered settlement/proof-mining state unless sequence grammar, verifier unit, claimability, and recovery roots agree",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/integration/test_dex_engine_settlement_sequence_grammar_fuzz.py",
                "tests/integration/test_proof_verifier_unit.py",
                "tests/integration/test_proof_mining_claimability.py",
                "tests/integration/test_tau_testnet_dex_plugin_recovery.py",
            ),
        ),
    },
    {
        "axis_id": "acceptance_tcb_minimized_witness_boundary",
        "priority_score": -56,
        "surface_ids": (
            "stale_settlement_boundary",
            "quote_receipt_certificate_boundary",
            "api_request_authorization_boundary",
        ),
        "what_if": "Acceptance-TCB campaign outputs, minimized witness diffs, and query interfaces disagree about which disaster witnesses remain replayable.",
        "disaster_state_template": "minimized TCB witness is accepted or queried after its acceptance campaign root changes",
        "mutation_families": (
            "acceptance campaign root changes after minimized witness publication",
            "diff query returns a witness whose replay command no longer matches the campaign bundle",
            "minimized witness list omits a still-reachable replay seed",
        ),
        "bounded_harness_ideas": (
            "compose campaign, diff, and query tests as one minimized-witness lifecycle lane",
            "reject TCB promotion unless minimized witnesses, diffs, and query results share one replay root",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/integration/test_acceptance_tcb_fuzz_campaign.py",
                "tests/integration/test_diff_acceptance_tcb_minimized_witnesses.py",
                "tests/integration/test_query_acceptance_tcb_minimized_witnesses.py",
            ),
        ),
    },
    {
        "axis_id": "rc1_release_readiness_artifact_boundary",
        "priority_score": -57,
        "surface_ids": (
            "api_request_authorization_boundary",
            "quote_receipt_certificate_boundary",
            "stale_settlement_boundary",
        ),
        "what_if": "RC1 candidate, readiness, release snapshot, and verified surface matrix artifacts describe neighboring but different assured runtime surfaces.",
        "disaster_state_template": "release-ready artifact advertises an assurance surface not covered by the candidate/readiness evidence root",
        "mutation_families": (
            "RC1 candidate report changes after readiness snapshot construction",
            "assurance release snapshot includes a surface absent from verified surface matrix",
            "verified surface matrix row points to a stale candidate artifact",
        ),
        "bounded_harness_ideas": (
            "run RC1 candidate, report, readiness, release snapshot, and matrix rendering together",
            "reject release promotion unless candidate, readiness, snapshot, and matrix artifacts agree on the same covered surfaces",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/integration/test_rc1_candidate.py",
                "tests/integration/test_rc1_candidate_report.py",
                "tests/integration/test_rc1_readiness.py",
                "tests/tools/test_render_assurance_release_snapshot.py",
                "tests/tools/test_render_rc1_verified_surface_matrix.py",
            ),
        ),
    },
    {
        "axis_id": "advisory_swap_sandwich_preflight_boundary",
        "priority_score": -58,
        "surface_ids": (
            "api_request_authorization_boundary",
            "route_canonicalization_boundary",
            "quote_receipt_certificate_boundary",
        ),
        "what_if": "Swap preflight, guardrail advice, volatility tiers, price-impact previews, and sandwich-risk estimates individually pass but disagree on the same proposed swap.",
        "disaster_state_template": "advisory-safe swap crosses a neighboring guardrail or sandwich-risk boundary",
        "mutation_families": (
            "price-impact preview returns safe while sandwich risk reports exploitable profit",
            "volatility tier changes after pokayoke guardrail decision",
            "dynamic-fee sandwich boundary accepts a swap rejected by preflight",
        ),
        "bounded_harness_ideas": (
            "run swap preflight, guardrail, price impact, volatility, and sandwich-risk tests as one advisory lane",
            "reject advisory promotion unless all non-consensus risk views agree on reject/safe boundaries",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/core/test_pokayoke_swap_guardrails.py",
                "tests/core/test_pokayoke_swap_suggest.py",
                "tests/core/test_price_impact_preview.py",
                "tests/core/test_sandwich_dynamic_fee.py",
                "tests/core/test_sandwich_risk.py",
                "tests/core/test_swap_preflight.py",
                "tests/core/test_volatility_tier.py",
                "tests/core/test_volatility_tier_ref_parity.py",
            ),
        ),
    },
    {
        "axis_id": "functional_core_split_parity_branch_boundary",
        "priority_score": -59,
        "surface_ids": (
            "route_canonicalization_boundary",
            "quote_receipt_certificate_boundary",
            "api_request_authorization_boundary",
        ),
        "what_if": "Reference parity, branch-edge coverage, split routing, and no-float functional-core checks pass in isolation while a composed route branch escapes a declared deterministic domain.",
        "disaster_state_template": "branch-covered functional-core path disagrees with reference parity or deterministic split-routing dispatch",
        "mutation_families": (
            "split routing dispatch changes candidate order without ref-parity drift",
            "branch-edge fixture covers a route rejected by no-float functional-core policy",
            "curve-selection ref parity passes while split-routing branch chooses a neighboring pool family",
        ),
        "bounded_harness_ideas": (
            "compose functional-core parity, branch-edge, split-routing, and no-float tests",
            "reject functional-core route promotion unless split dispatch, parity refs, and branch edges agree",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/core/test_cpmm_ref_parity.py",
                "tests/core/test_curve_selection_ref_parity.py",
                "tests/core/test_derivatives_generated_refs.py",
                "tests/core/test_functional_core_no_floats.py",
                "tests/core/test_misc_branch_coverage_edges.py",
                "tests/core/test_next_branch_coverage_edges.py",
                "tests/core/test_split_routing.py",
                "tests/core/test_split_routing_dispatch.py",
            ),
        ),
    },
    {
        "axis_id": "fire_cal_package_claim_boundary",
        "priority_score": -60,
        "surface_ids": (
            "settlement_attestation_policy_boundary",
            "stale_settlement_boundary",
            "quote_receipt_certificate_boundary",
        ),
        "what_if": "CAL/FIRE package receipts, cert files, FMOS files, formal claims, and generic parity packs agree syntactically but bind different package or proof roots.",
        "disaster_state_template": "formal package claim survives receipt or parity-root drift",
        "mutation_families": (
            "CAL/FIRE receipt binding changes after FIRE cert construction",
            "FMOS file root differs from formal assurance claim root",
            "canonical plateau or dust/carry pack validates against a stale parity receipt",
        ),
        "bounded_harness_ideas": (
            "run CAL/FIRE package binding, cert, FMOS, formal claims, parity, plateau, and dust/carry checks together",
            "reject package promotion unless cert, FMOS, claim, and parity roots are co-bound",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/kernels/test_cal_fire_logic_package_receipt_binding.py",
                "tests/kernels/test_fire_cert_v1.py",
                "tests/kernels/test_fire_fmos_file_v1.py",
                "tests/kernels/test_fire_formal_assurance_claims.py",
                "tests/tools/test_check_parity_v1.py",
                "tests/tools/test_check_canonical_plateau_pack_v1.py",
                "tests/tools/test_check_dust_and_carry_pack_v1.py",
            ),
        ),
    },
    {
        "axis_id": "tokenomics_wash_budget_boundary",
        "priority_score": -61,
        "surface_ids": (
            "api_request_authorization_boundary",
            "settlement_attestation_policy_boundary",
            "stale_settlement_boundary",
        ),
        "what_if": "Wash-trade, pro-rata budget, POL-share safety, wash inversion, and bonus-bet model checks validate local economics but compose into an exploitable reward or budget state.",
        "disaster_state_template": "tokenomics-local no-profit result permits cross-budget wash or bonus extraction",
        "mutation_families": (
            "wash sequence passes while pro-rata budget is exhausted",
            "wash math inversion disagrees with POL share required for safety",
            "bonus-bet model credits value after wash-trade reject path",
        ),
        "bounded_harness_ideas": (
            "compose wash, inversion, pro-rata, POL-share, and bonus-budget tests",
            "reject tokenomics promotion unless local anti-wash and global budget constraints agree",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/tools/test_tokenomics_wash_trade.py",
                "tests/tools/test_tokenomics_wash_trade_sequence.py",
                "tests/tools/test_wash_math_inversion.py",
                "tests/tools/test_tokenomics_pro_rata_budget.py",
                "tests/tools/test_tokenomics_pol_share_required_for_safety.py",
                "tests/core/test_bonus_bet_model.py",
            ),
        ),
    },
    {
        "axis_id": "decision_tau_witness_runner_boundary",
        "priority_score": -62,
        "surface_ids": (
            "api_request_authorization_boundary",
            "operations_signature_reuse_boundary",
            "settlement_attestation_policy_boundary",
        ),
        "what_if": "Decision witnesses, adapters, Tau witness construction, and fake-runner utilities agree in no-skip mode while the real runner remains an external dependency.",
        "disaster_state_template": "decision witness accepted by adapters but encoded into a Tau witness the deterministic runner rejects",
        "mutation_families": (
            "decision witness adapter normalizes fields differently from Tau witness builder",
            "fake Tau runner accepts an output shape rejected by runner utility checks",
            "decision witness omits a field later required by Tau witness construction",
        ),
        "bounded_harness_ideas": (
            "compose decision witness, adapter, Tau witness, fake-runner, and runner utility checks",
            "keep external Tau-binary skips out of unreachable claims and require deterministic runner parity first",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/integration/test_decision_witness.py",
                "tests/integration/test_decision_witness_adapters.py",
                "tests/integration/test_tau_witness.py",
                "tests/integration/test_tau_runner_fake_tau.py",
                "tests/integration/test_tau_runner_utils.py",
            ),
        ),
    },
    {
        "axis_id": "optimizer_liveness_prompt_boundary",
        "priority_score": -63,
        "surface_ids": (
            "route_canonicalization_boundary",
            "api_request_authorization_boundary",
            "quote_receipt_certificate_boundary",
        ),
        "what_if": "Optimizer audited-bounds liveness, liveness v2, and LTLF prompt A/B harnesses prove neighboring progress notions for the same route search surface.",
        "disaster_state_template": "optimizer appears live under one audited-bounds prompt but stalls or exceeds bounds under a neighboring liveness contract",
        "mutation_families": (
            "audited bounds v1 accepts a liveness trace rejected by v2",
            "optimizer liveness v2 passes while prompt A/B harness classifies the same trace as stalled",
            "route search progress proof omits an API-bound resource constraint",
        ),
        "bounded_harness_ideas": (
            "compose optimizer liveness, audited bounds, and prompt A/B tests",
            "reject liveness promotion unless route progress, audited bounds, and prompt harness agree",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/formal/test_esso_optimizer_audited_bounds_liveness.py",
                "tests/formal/test_esso_optimizer_audited_bounds_liveness_v2.py",
                "tests/formal/test_optimizer_liveness_v2.py",
                "tests/tools/test_ltlf_prompt_ab_harness.py",
            ),
        ),
    },
    {
        "axis_id": "chaos_regret_campaign_boundary",
        "priority_score": -64,
        "surface_ids": (
            "api_request_authorization_boundary",
            "settlement_attestation_policy_boundary",
            "stale_settlement_boundary",
        ),
        "what_if": "Chaos regret scheduling, toolkit artifacts, and repo campaign runners report successful recovery while the same artifact set would not replay under the bounded disaster runner.",
        "disaster_state_template": "chaos campaign artifact is treated as recovered without replayable regret or runner evidence",
        "mutation_families": (
            "regret scheduler output changes after toolkit artifact capture",
            "repo campaign runner writes an artifact root not accepted by chaos toolkit checks",
            "chaos recovery report omits the replay seed needed for disaster reproduction",
        ),
        "bounded_harness_ideas": (
            "compose chaos scheduler, toolkit artifact, and repo campaign tests",
            "reject chaos recovery claims unless campaign artifacts are replayable by the same bounded runner",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/chaos/test_chaos_regret_scheduler.py",
                "tests/chaos/test_chaos_toolkit_runner_artifacts.py",
                "tests/chaos/test_run_repo_campaign.py",
            ),
        ),
    },
    {
        "axis_id": "autotrader_krr_import_supply_chain_boundary",
        "priority_score": -65,
        "surface_ids": (
            "api_request_authorization_boundary",
            "operations_signature_reuse_boundary",
            "nonce_replay_guard",
        ),
        "what_if": "Autotrader KRR bundle, history, source import, and Wikidata import tools produce a policy knowledge root that can drift from the action authorization surface.",
        "disaster_state_template": "KRR-imported policy fact survives history or source-root drift and authorizes a stale strategy action",
        "mutation_families": (
            "KRR bundle build accepts facts imported under a stale source root",
            "policy history replay changes after Wikidata import normalization",
            "imported source fact authorizes a strategy action outside current KRR bundle root",
        ),
        "bounded_harness_ideas": (
            "compose KRR bundle, history, source import, and Wikidata import CLI tests",
            "reject KRR-backed policy promotion unless imported facts and policy history share one bundle root",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/integration/test_autotrader_krr_bundle_build_cli.py",
                "tests/integration/test_autotrader_krr_history_cli.py",
                "tests/integration/test_autotrader_krr_import_source_cli.py",
                "tests/integration/test_autotrader_krr_import_wikidata_cli.py",
            ),
        ),
    },
    {
        "axis_id": "amm_curve_il_parity_boundary",
        "priority_score": -66,
        "surface_ids": (
            "route_canonicalization_boundary",
            "quote_receipt_certificate_boundary",
            "stale_settlement_boundary",
        ),
        "what_if": "Alternative AMM curves, IL futures, homological arbitrage, and sealed-bid bond checks each pass while cross-curve route or settlement value semantics diverge.",
        "disaster_state_template": "curve-local value proof composes into cross-curve route or settlement value drift",
        "mutation_families": (
            "IL futures ref parity passes while route value differs across AMM family",
            "homological arbitrage witness crosses a curve family with mismatched sealed-bid bond semantics",
            "mobius/power/quadratic/sum-boost curve boundary changes settlement value without receipt drift",
        ),
        "bounded_harness_ideas": (
            "compose alternative curve, IL futures, homological arbitrage, and sealed-bid bond tests",
            "reject cross-curve route promotion unless curve-local value and parity checks agree",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/core/test_homological_arbitrage.py",
                "tests/core/test_il_futures.py",
                "tests/core/test_il_futures_ref_parity.py",
                "tests/core/test_mobius_cpmm.py",
                "tests/core/test_power_product_cpmm.py",
                "tests/core/test_quadratic_cpmm.py",
                "tests/core/test_sum_boost_amm.py",
                "tests/core/test_sealed_bid_bonds.py",
            ),
        ),
    },
    {
        "axis_id": "lean_amm_canonical_math_boundary",
        "priority_score": -67,
        "surface_ids": (
            "route_canonicalization_boundary",
            "quote_receipt_certificate_boundary",
            "settlement_attestation_policy_boundary",
        ),
        "what_if": "Lean proofs for arbitrage certificates, CPMM monotonicity, split certificates, opposite-direction noncommutativity, rounding, and canonical winners describe incompatible mathematical envelopes.",
        "disaster_state_template": "proved local AMM theorem leaves a gap in route canonicality or rounding witness composition",
        "mutation_families": (
            "canonical winner proof assumes a rounding envelope not shared by route certificate",
            "Galois split certificate admits a path excluded by opposite-direction noncommutativity",
            "CPMM monotonicity proof disagrees with arbitrage certificate boundary case",
        ),
        "bounded_harness_ideas": (
            "compose Lean AMM, rounding, split, and canonical-winner tests",
            "reject mathematical promotion unless theorem wrappers cover one shared bounded AMM envelope",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/formal/test_lean_arbitrage_certificate.py",
                "tests/formal/test_lean_cpmm_output_monotonicity.py",
                "tests/formal/test_lean_galois_split_certificate.py",
                "tests/formal/test_lean_opposite_direction_noncommutativity.py",
                "tests/formal/test_lean_rounding.py",
                "tests/formal/test_lean_rounding_error_bound.py",
                "tests/formal/test_lean_unique_canonical_winner_everywhere.py",
            ),
        ),
    },
    {
        "axis_id": "lean_repair_economics_boundary",
        "priority_score": -68,
        "surface_ids": (
            "stale_settlement_boundary",
            "settlement_attestation_policy_boundary",
            "api_request_authorization_boundary",
        ),
        "what_if": "Repair-economics Lean proofs for disclosure, queue discipline, treasury budget, principal games, slash policy, and self-exploit impossibility prove local mechanisms but not cross-incident composition.",
        "disaster_state_template": "repair-local theorem permits multi-incident treasury or disclosure state drift",
        "mutation_families": (
            "multi-incident conservation proof disagrees with treasury budget proof",
            "repair queue discipline allows a disclosure window rejected by slash adjudication policy",
            "principal payoff proof admits a state steering path blocked by self-exploit impossibility",
        ),
        "bounded_harness_ideas": (
            "compose repair canonicality, disclosure, treasury, principal game, slash, queue, and self-exploit proof wrappers",
            "reject repair promotion unless incident, treasury, principal, and queue theorem surfaces agree",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/formal/test_lean_repair_canonical_selection.py",
                "tests/formal/test_lean_repair_disclosure_selection.py",
                "tests/formal/test_lean_repair_disclosure_treasury_interaction.py",
                "tests/formal/test_lean_repair_disclosure_window.py",
                "tests/formal/test_lean_repair_endogenous_withholding_game.py",
                "tests/formal/test_lean_repair_fund_dominated_withholding_game.py",
                "tests/formal/test_lean_repair_incident_value_bridge.py",
                "tests/formal/test_lean_repair_multi_incident_conservation.py",
                "tests/formal/test_lean_repair_pairwise_headroom_competition.py",
                "tests/formal/test_lean_repair_principal_best_response_game.py",
                "tests/formal/test_lean_repair_principal_payoff_competition.py",
                "tests/formal/test_lean_repair_principal_state_steering.py",
                "tests/formal/test_lean_repair_queue_discipline.py",
                "tests/formal/test_lean_repair_self_exploit_impossibility.py",
                "tests/formal/test_lean_repair_split_principal_competition_game.py",
                "tests/formal/test_lean_repair_split_principal_external_recapture_game.py",
                "tests/formal/test_lean_repair_split_principal_internalization_game.py",
                "tests/formal/test_lean_repair_split_principal_slash_adjudication.py",
                "tests/formal/test_lean_repair_split_principal_slash_adjudication_policy.py",
                "tests/formal/test_lean_repair_split_principal_slash_policy.py",
                "tests/formal/test_lean_repair_split_principal_treasury_internalization.py",
                "tests/formal/test_lean_repair_split_principal_treasury_transition.py",
                "tests/formal/test_lean_repair_treasury_budget.py",
                "tests/formal/test_lean_repair_withholding_treasury_competition.py",
            ),
        ),
    },
    {
        "axis_id": "lean_autotrader_solver_policy_boundary",
        "priority_score": -69,
        "surface_ids": (
            "api_request_authorization_boundary",
            "operations_signature_reuse_boundary",
            "nonce_replay_guard",
        ),
        "what_if": "Lean autotrader, agent capability, solver-checker separation, and payoff-language proofs validate neighboring policy semantics for the same live action.",
        "disaster_state_template": "solver-checked autotrader action crosses a capability or payoff-language proof boundary",
        "mutation_families": (
            "autotrader stage certificate proof binds a different action than live release proof",
            "agent capability bound permits a decision rejected by binary decision proof",
            "solver-checker separation proof accepts a payoff-language witness with stale policy fields",
        ),
        "bounded_harness_ideas": (
            "compose Lean autotrader, capability, solver-checker, and payoff-language tests",
            "reject policy promotion unless decision, stage, live release, capability, solver, and payoff proofs agree",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/formal/test_lean_agent_capability_bounds.py",
                "tests/formal/test_lean_autotrader_binary_decision.py",
                "tests/formal/test_lean_autotrader_decision_binding.py",
                "tests/formal/test_lean_autotrader_live_release_certificate.py",
                "tests/formal/test_lean_autotrader_stage_certificate.py",
                "tests/formal/test_lean_solver_checker_separation.py",
                "tests/formal/test_lean_zeno_payoff_language.py",
            ),
        ),
    },
    {
        "axis_id": "krr_region_ba_reasoner_boundary",
        "priority_score": -70,
        "surface_ids": (
            "api_request_authorization_boundary",
            "route_canonicalization_boundary",
            "settlement_attestation_policy_boundary",
        ),
        "what_if": "KRR reasoner, autonomous Lean classification, deep hypothesis discovery, Metamuse workflow, and region BA checks promote a hypothesis whose region semantics disagree with the executable surface.",
        "disaster_state_template": "reasoner-promoted hypothesis outlives region BA or Lean-classification evidence",
        "mutation_families": (
            "KRR reasoner fact changes after region BA report construction",
            "autonomous Lean classification promotes a hypothesis absent from executable region checks",
            "Metamuse workflow emits a candidate whose region BA semantics are stale",
        ),
        "bounded_harness_ideas": (
            "compose KRR reasoner, Lean classification, deep hypothesis, Metamuse, and region BA tests",
            "reject hypothesis promotion unless reasoner, classifier, workflow, and region evidence agree",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/tools/test_krr_reasoner_engine.py",
                "tests/tools/test_zenodex_autonomous_checks_lean_classification.py",
                "tests/tools/test_zenodex_deep_hypothesis_pack_discovery.py",
                "tests/tools/test_zenodex_metamuse_workflow.py",
                "tests/integration/test_region_ba.py",
            ),
        ),
    },
    {
        "axis_id": "tool_guard_lint_symbolic_boundary",
        "priority_score": -71,
        "surface_ids": (
            "api_request_authorization_boundary",
            "quote_receipt_certificate_boundary",
            "route_canonicalization_boundary",
        ),
        "what_if": "Pokayoke audit, system-spec lint, Sympy ESSO guard lint, and Sympy Tau guard normalization accept syntactically different guard languages for the same policy.",
        "disaster_state_template": "lint-clean symbolic guard normalizes into a different runtime policy",
        "mutation_families": (
            "Sympy Tau normalizer changes a guard accepted by system-spec lint",
            "ESSO guard lint passes while pokayoke audit flags a neighboring policy",
            "symbolic guard normalization drops a condition required by runtime request admission",
        ),
        "bounded_harness_ideas": (
            "compose pokayoke audit, system-spec lint, ESSO guard lint, and Tau normalizer tests",
            "reject symbolic guard promotion unless all guard-language lints agree",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/tools/test_pokayoke_audit_tool.py",
                "tests/tools/test_system_spec_lint.py",
                "tests/tools/test_sympy_esso_guard_lint.py",
                "tests/tools/test_sympy_tau_guard_normalizer.py",
            ),
        ),
    },
    {
        "axis_id": "zusd_support_native_selector_boundary",
        "priority_score": -72,
        "surface_ids": (
            "settlement_attestation_policy_boundary",
            "stale_settlement_boundary",
            "api_request_authorization_boundary",
        ),
        "what_if": "zUSD support-root logic, multi-oracle commit native adapter, and multi-redeem selector native adapter agree locally but diverge under support/root or oracle-region drift.",
        "disaster_state_template": "support-root-valid zUSD selector admits a stale oracle or redeem state",
        "mutation_families": (
            "support root changes after multi-oracle commit witness construction",
            "multi-redeem selector accepts a vault state rejected by native oracle commit adapter",
            "zUSD support-root proof omits a risky selector boundary case",
        ),
        "bounded_harness_ideas": (
            "compose support-root, multi-oracle commit adapter, and multi-redeem selector adapter checks",
            "reject zUSD selector promotion unless support, oracle commit, and redeem selector roots agree",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/core/test_support_root.py",
                "tests/kernels/test_zusd_multi_oracle_commit_mcr_v1_native_adapter.py",
                "tests/kernels/test_zusd_multi_redeem_selector_v1_native_adapter.py",
            ),
        ),
    },
    {
        "axis_id": "lean_cross_surface_composition_boundary",
        "priority_score": -73,
        "surface_ids": (
            "settlement_attestation_policy_boundary",
            "route_canonicalization_boundary",
            "quote_receipt_certificate_boundary",
        ),
        "what_if": "Lean cross-protocol, cross-surface benefit, defensive liquidity, exploit-repair composition, fee-aware, role-collapse, and two-venue governance proofs validate different composed DEX worlds.",
        "disaster_state_template": "cross-surface theorem family permits a benefit, role, or venue state rejected by another composition proof",
        "mutation_families": (
            "cross-surface benefit budget proof disagrees with defensive liquidity benefit",
            "two-venue governance proof permits a role-collapse state rejected by release gate",
            "fee-aware anti-fragmentation proof disagrees with exploit-repair composition boundary",
        ),
        "bounded_harness_ideas": (
            "compose cross-protocol, cross-surface, defensive liquidity, exploit-repair, fee-aware, role, and two-venue Lean tests",
            "reject cross-surface promotion unless the theorem wrappers share one model envelope",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/formal/test_lean_cross_protocol_recapture_gate.py",
                "tests/formal/test_lean_cross_surface_benefit_budget.py",
                "tests/formal/test_lean_defensive_liquidity_benefit.py",
                "tests/formal/test_lean_exploit_repair_composition.py",
                "tests/formal/test_lean_fee_aware_anti_fragmentation.py",
                "tests/formal/test_lean_fee_aware_batch_k_gap.py",
                "tests/formal/test_lean_role_collapse_release_gate.py",
                "tests/formal/test_lean_two_venue_composition.py",
                "tests/formal/test_lean_two_venue_governance_composition.py",
            ),
        ),
    },
    {
        "axis_id": "operator_environment_tooling_boundary",
        "priority_score": -74,
        "surface_ids": (
            "api_request_authorization_boundary",
            "settlement_attestation_policy_boundary",
            "operations_signature_reuse_boundary",
        ),
        "what_if": "Operator systemd generation, Runpod ESSO workflow helpers, ESSO feature reports, and CHC verification wrappers accept an environment that cannot replay the intended operator evidence.",
        "disaster_state_template": "operator environment tool emits a runnable-looking setup whose verification or feature evidence is stale",
        "mutation_families": (
            "systemd unit points to a verification environment different from ESSO feature report",
            "Runpod helper captures artifacts that CHC verification wrapper cannot replay",
            "operator environment changes after feature report construction",
        ),
        "bounded_harness_ideas": (
            "compose operator systemd, Runpod, feature report, and CHC wrapper tests",
            "reject operator environment promotion unless generated runtime and verification artifacts replay together",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/tools/test_generate_operator_systemd.py",
                "tests/tools/test_runpod_esso.py",
                "tests/tools/test_esso_feature_report.py",
                "tests/tools/test_esso_verify_chc.py",
            ),
        ),
    },
    {
        "axis_id": "stateful_bounty_catalog_feedback_boundary",
        "priority_score": -75,
        "surface_ids": (
            "stale_settlement_boundary",
            "quote_receipt_certificate_boundary",
            "route_canonicalization_boundary",
        ),
        "what_if": "Improvement-bounty routes, sealed-bid disaster catalog entries, RC1 candidate index, and stateful feedback reports agree locally but publish different search priorities.",
        "disaster_state_template": "bounty or catalog promotion hides a still-priority disaster surface from stateful feedback",
        "mutation_families": (
            "improvement bounty route changes after stateful feedback report construction",
            "sealed-bid disaster catalog omits a candidate promoted by RC1 candidate index",
            "stateful feedback ranking downgrades a disaster surface still present in bounty route evidence",
        ),
        "bounded_harness_ideas": (
            "compose improvement bounty, sealed-bid catalog, RC1 candidate index, and stateful feedback tests",
            "reject promotion unless bounty, catalog, candidate index, and feedback priorities agree",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/tools/test_improvement_bounty_round_route_v1.py",
                "tests/tools/test_sealed_bid_disaster_catalog.py",
                "tests/integration/test_rc1_candidate_index.py",
                "tests/integration/test_stateful_feedback.py",
            ),
        ),
    },
    {
        "axis_id": "batch_settler_greedy_adapter_boundary",
        "priority_score": -76,
        "surface_ids": (
            "stale_settlement_boundary",
            "route_canonicalization_boundary",
            "quote_receipt_certificate_boundary",
        ),
        "what_if": "Batch auction native adapter and Lean greedy approximation wrappers accept neighboring candidate orders or approximation bounds.",
        "disaster_state_template": "batch-settler adapter accepts a clearing order outside the Lean greedy approximation envelope",
        "mutation_families": (
            "native batch-settler adapter selects an order outside greedy approximation bounds",
            "Lean greedy approximation proof permits a candidate rejected by adapter witness shape",
            "batch candidate tie changes while approximation proof root remains stable",
        ),
        "bounded_harness_ideas": (
            "compose batch auction native adapter and Lean greedy approximation checks",
            "reject batch-greedy promotion unless adapter witness and approximation proof share candidate-order semantics",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/kernels/test_batch_auction_settler_v1_adapter.py",
                "tests/formal/test_lean_batch_greedy_approximation.py",
            ),
        ),
    },
    {
        "axis_id": "exact_out_adaptive_region_boundary",
        "priority_score": -77,
        "surface_ids": (
            "route_canonicalization_boundary",
            "quote_receipt_certificate_boundary",
            "api_request_authorization_boundary",
        ),
        "what_if": "Exact-out adaptive liveness region checks pass even though long benchmark lanes remain too expensive for the disaster runner.",
        "disaster_state_template": "region-valid exact-out adaptive path hides an unbounded benchmark or liveness cost",
        "mutation_families": (
            "adaptive region boundary accepts a path whose benchmark lane exceeds the disaster-runner cap",
            "region certificate covers a route path omitted by long benchmark exploration",
            "exact-out adaptive liveness region changes without matching resource-bound witness",
        ),
        "bounded_harness_ideas": (
            "promote the fast adaptive region lane while keeping benchmark timeout lanes as explicit backlog",
            "reject exact-out adaptive promotion unless region checks and resource-bound receipts remain separate",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/integration/test_exact_out_many_pool_adaptive_liveness_regions.py",
            ),
        ),
    },
    {
        "axis_id": "shapeforge_release_ratchet_artifact_boundary",
        "priority_score": -78,
        "surface_ids": (
            "api_request_authorization_boundary",
            "settlement_attestation_policy_boundary",
            "quote_receipt_certificate_boundary",
        ),
        "what_if": "ShapeForge release bundles, ratchets, explorer extraction, target-shape comparison, and validation artifacts agree while target-eval expectations remain stale.",
        "disaster_state_template": "ShapeForge release artifact passes ratchet validation but points to stale target-shape semantics",
        "mutation_families": (
            "release bundle passes after target-shape comparison root changes",
            "ratchet check accepts a ShapeForge artifact whose explorer extraction is stale",
            "ShapeForge validation passes while target-eval support counts remain backlog",
        ),
        "bounded_harness_ideas": (
            "compose ShapeForge release, ratchet, explorer, comparison, and validation tests without stale target-eval expectations",
            "reject ShapeForge promotion unless release bundle, ratchet, extraction, comparison, and validation roots agree",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/tools/test_build_shape_v1_release_bundle.py",
                "tests/tools/test_check_shape_v1_ratchet.py",
                "tests/tools/test_check_shape_v1_release_bundle.py",
                "tests/tools/test_shapeforge_extract_explorer.py",
                "tests/tools/test_shapeforge_target_shape_compare.py",
                "tests/tools/test_shapeforge_validate.py",
            ),
        ),
    },
    {
        "axis_id": "zenograph_autotrader_ranking_artifact_boundary",
        "priority_score": -79,
        "surface_ids": (
            "api_request_authorization_boundary",
            "operations_signature_reuse_boundary",
            "nonce_replay_guard",
        ),
        "what_if": "Zenograph autotrader adapters, ranking review bundles, campaign reports, stage summaries, shadow comparisons, and fact packs promote different strategy states.",
        "disaster_state_template": "Zenograph ranking artifact promotes a strategy action from a stale shadow or fact-pack root",
        "mutation_families": (
            "ranking review bundle verifies after shadow baseline changes",
            "Zenograph fact pack root changes after ranking stage summary construction",
            "autotrader adapter accepts a strategy state absent from campaign report evidence",
        ),
        "bounded_harness_ideas": (
            "compose Zenograph autotrader adapter, ranking, review, shadow, fact-pack, and stage tests",
            "reject ranking promotion unless adapter, review, campaign, shadow, fact-pack, and stage artifacts share one strategy root",
        ),
        "commands": (
            (
                "pytest",
                "-q",
                "tests/integration/test_zenograph_autotrader_adapter.py",
                "tests/integration/test_zenograph_autotrader_ranking_promotion_gate_cli.py",
                "tests/integration/test_zenograph_autotrader_ranking_review_bundle_cli.py",
                "tests/integration/test_zenograph_autotrader_ranking_review_bundle_verify_cli.py",
                "tests/integration/test_zenograph_autotrader_ranking_review_campaign_report_cli.py",
                "tests/integration/test_zenograph_autotrader_ranking_stage_cli.py",
                "tests/integration/test_zenograph_autotrader_ranking_stage_summary_cli.py",
                "tests/integration/test_zenograph_autotrader_shadow_cli.py",
                "tests/integration/test_zenograph_autotrader_shadow_compare_baseline.py",
                "tests/integration/test_zenograph_autotrader_shadow_compare_cli.py",
                "tests/integration/test_zenograph_fact_pack_cli.py",
                "tests/integration/test_zenograph_fact_pack_from_store_cli.py",
                "tests/integration/test_zenograph_ranking_review_bundle_verify.py",
                "tests/integration/test_zenograph_ranking_review_summary.py",
                "tests/integration/test_zenograph_ranking_stage.py",
                "tests/integration/test_zenograph_ranking_stage_summary.py",
            ),
        ),
    },
)


def _relpath(path: Path) -> str:
    try:
        return str(path.resolve().relative_to(REPO_ROOT))
    except ValueError:
        return str(path)


def _resolve_path(path: str | Path | None) -> Path | None:
    if path is None:
        return None
    raw = Path(path)
    if raw.is_absolute():
        return raw
    return REPO_ROOT / raw


def _load_json(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: JSON payload must be an object")
    return payload


def _require_text(errors: list[str], payload: dict[str, Any], key: str) -> str | None:
    value = payload.get(key)
    if not isinstance(value, str) or not value.strip():
        errors.append(f"{key} must be a non-empty string")
        return None
    return value.strip()


def _require_text_list(errors: list[str], value: object, key: str, *, nonempty: bool) -> list[str]:
    if not isinstance(value, list):
        errors.append(f"{key} must be a list")
        return []
    rows: list[str] = []
    for idx, item in enumerate(value):
        if not isinstance(item, str) or not item.strip():
            errors.append(f"{key}[{idx}] must be a non-empty string")
            continue
        rows.append(item.strip())
    if nonempty and not rows:
        errors.append(f"{key} must contain at least one string")
    return rows


def _surfaces_by_id(target_manifest: Path) -> dict[str, DangerousSurface]:
    return {surface.id: surface for surface in load_dangerous_surface_manifest(target_manifest)}


def _evidence_at_most(value: str, ceiling: str) -> bool:
    return EVIDENCE_ORDER.get(value, 999) <= EVIDENCE_ORDER[ceiling]


def _campaign_defaults(candidate: dict[str, Any]) -> dict[str, Any]:
    campaign = candidate.get("campaign", {})
    if not isinstance(campaign, dict):
        campaign = {}
    gate_lane = campaign.get("gate_lane", "deep")
    feedback_mode = campaign.get("feedback_mode", "stateful")
    include_slow = bool(campaign.get("include_slow_explorers", False))
    return {
        "gate_lane": gate_lane if gate_lane in {"fast", "deep"} else "deep",
        "feedback_mode": feedback_mode if feedback_mode in {"legacy", "stateful"} else "stateful",
        "include_slow_explorers": include_slow,
    }


def _scenario_replay_command(*, surface_id: str, campaign: dict[str, Any], target_manifest: Path) -> list[str]:
    command = [
        "python3",
        "tools/acceptance_tcb_fuzz_campaign.py",
        "--gate-lane",
        str(campaign["gate_lane"]),
        "--target-id",
        surface_id,
        "--feedback-mode",
        str(campaign["feedback_mode"]),
        "--stateful-exploration",
        "--target-manifest",
        _relpath(target_manifest),
        "--format",
        "json",
    ]
    if campaign["include_slow_explorers"]:
        command.append("--include-slow-explorers")
    return command


def check_scenario_candidate(
    candidate: dict[str, Any],
    *,
    target_manifest: str | Path = DEFAULT_TARGET_MANIFEST,
) -> dict[str, Any]:
    manifest_path = _resolve_path(target_manifest)
    if manifest_path is None or not manifest_path.is_file():
        raise ValueError(f"missing dangerous-surface manifest: {target_manifest}")

    errors: list[str] = []
    warnings: list[str] = []
    if candidate.get("schema") != SCENARIO_CANDIDATE_SCHEMA:
        errors.append(f"schema must equal {SCENARIO_CANDIDATE_SCHEMA}")

    scenario_id = _require_text(errors, candidate, "scenario_id")
    surface_id = _require_text(errors, candidate, "surface_id")
    disaster_state = _require_text(errors, candidate, "disaster_state")
    action_grammar = _require_text(errors, candidate, "action_grammar")
    expected_guard = _require_text(errors, candidate, "expected_guard")

    bounds = candidate.get("bounds")
    if not isinstance(bounds, dict):
        errors.append("bounds must be an object")
        bounds = {}
    max_depth = bounds.get("max_depth")
    max_frontier = bounds.get("max_frontier")
    if not isinstance(max_depth, int) or max_depth < 0:
        errors.append("bounds.max_depth must be an integer >= 0")
    if not isinstance(max_frontier, int) or max_frontier <= 0:
        errors.append("bounds.max_frontier must be an integer > 0")

    oracle = candidate.get("oracle")
    if not isinstance(oracle, dict):
        errors.append("oracle must be an object")
        oracle = {}
    expected_tokens = _require_text_list(
        errors,
        oracle.get("expected_outcome_tokens"),
        "oracle.expected_outcome_tokens",
        nonempty=True,
    )
    forbidden_tokens = _require_text_list(
        errors,
        oracle.get("forbidden_outcome_tokens", []),
        "oracle.forbidden_outcome_tokens",
        nonempty=False,
    )

    promotion_target = candidate.get("promotion_target")
    if not isinstance(promotion_target, dict):
        errors.append("promotion_target must be an object")
        promotion_target = {}
    promotion_kind = promotion_target.get("kind")
    if promotion_kind not in {"shapeforge_scenario", "dangerous_surface", "negative_knowledge"}:
        errors.append("promotion_target.kind must be shapeforge_scenario, dangerous_surface, or negative_knowledge")
    promotion_evidence = promotion_target.get("evidence_class", MAX_SCENARIO_EVIDENCE)
    if promotion_evidence not in EVIDENCE_ORDER:
        errors.append("promotion_target.evidence_class must be a known evidence class")
    elif not _evidence_at_most(str(promotion_evidence), MAX_SCENARIO_EVIDENCE):
        errors.append("promotion_target.evidence_class cannot exceed tested_discovery for fuzz-derived candidates")

    evidence_ceiling = candidate.get("evidence_class_ceiling")
    if evidence_ceiling not in EVIDENCE_ORDER:
        errors.append("evidence_class_ceiling must be a known evidence class")
        evidence_ceiling = None
    elif not _evidence_at_most(str(evidence_ceiling), MAX_SCENARIO_EVIDENCE):
        errors.append("evidence_class_ceiling cannot exceed tested_discovery for LLM scenario candidates")

    surfaces = _surfaces_by_id(manifest_path)
    surface = surfaces.get(surface_id or "")
    matched_surface: dict[str, Any] | None = None
    if surface_id is not None and surface is None:
        errors.append(f"surface_id {surface_id!r} is not declared in the dangerous-surface manifest")
    elif surface is not None:
        matched_surface = {
            "id": surface.id,
            "machine_family": surface.machine_family,
            "invariant_boundary": surface.invariant_boundary,
            "action_grammar": surface.action_grammar,
            "harnesses": list(surface.harnesses),
            "outcome_tokens": list(surface.outcome_tokens),
            "witness_ids": list(surface.witness_ids),
        }
        if expected_tokens and not (set(expected_tokens) & set(surface.outcome_tokens)):
            errors.append("oracle.expected_outcome_tokens must include at least one manifest outcome token for the surface")
        harness_hint = candidate.get("harness_hint")
        if harness_hint is not None and harness_hint not in surface.harnesses:
            errors.append("harness_hint must name a harness declared for the selected surface")
        if action_grammar and action_grammar != surface.action_grammar:
            warnings.append("candidate action_grammar differs from the manifest grammar; treating it as a scenario refinement")

    campaign = _campaign_defaults(candidate)
    replay_command = (
        _scenario_replay_command(surface_id=surface_id, campaign=campaign, target_manifest=manifest_path)
        if surface_id
        else []
    )

    return {
        "schema": SCENARIO_CANDIDATE_CHECK_SCHEMA,
        "ok": not errors,
        "generated_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "errors": errors,
        "warnings": warnings,
        "scenario_id": scenario_id,
        "surface_id": surface_id,
        "disaster_state": disaster_state,
        "expected_guard": expected_guard,
        "forbidden_outcome_tokens": forbidden_tokens,
        "target_manifest": _relpath(manifest_path),
        "matched_surface": matched_surface,
        "evidence_class_ceiling": evidence_ceiling,
        "promotion_policy": {
            "candidate_only": True,
            "max_evidence_class": MAX_SCENARIO_EVIDENCE,
            "reason": "LLM scenario plus bounded fuzz/concolic evidence is not theorem-grade proof.",
        },
        "replay_plan": {
            "campaign": campaign,
            "command": replay_command,
        },
    }


def _load_artifact(report: dict[str, Any], campaign_report_path: Path, key: str, schema: str, errors: list[str]) -> dict[str, Any] | None:
    artifacts = report.get("artifacts")
    if not isinstance(artifacts, dict):
        errors.append("campaign report artifacts must be an object")
        return None
    raw_path = artifacts.get(key)
    if not isinstance(raw_path, str) or not raw_path:
        errors.append(f"campaign report missing artifacts.{key}")
        return None
    path = _resolve_path(raw_path)
    if path is None or not path.is_file():
        errors.append(f"missing artifact {key}: {raw_path}")
        return None
    try:
        payload = _load_json(path)
    except Exception as exc:
        errors.append(f"failed to read artifact {key}: {exc}")
        return None
    if payload.get("schema") != schema:
        errors.append(f"{_relpath(path)} schema must equal {schema}")
        return None
    payload["_artifact_path"] = _relpath(path)
    return payload


def _surface_axis(surface: DangerousSurface) -> str:
    haystack = f"{surface.id} {surface.machine_family} {' '.join(surface.waypoint_tags)}"
    if "canonicalization" in haystack or "routing" in haystack:
        return "canonical_key"
    if any(token in haystack for token in ("auth", "nonce", "signature", "receipt", "settlement", "attestation", "replay")):
        return "guard"
    return "operator"


def _improvement_target(surface: DangerousSurface, axis: str) -> str:
    if axis == "canonical_key":
        return "canonicalization"
    if "replay" in surface.id or "stale" in surface.id:
        return "replay_and_freshness_guard_alignment"
    return "fail_closed_admissibility"


def _guard_rows_by_surface(guard_report: dict[str, Any] | None) -> dict[str, list[dict[str, Any]]]:
    rows: dict[str, list[dict[str, Any]]] = {}
    if not guard_report:
        return rows
    for witness in guard_report.get("witnesses", []):
        if not isinstance(witness, dict):
            continue
        for surface_id in witness.get("surface_ids", []):
            if isinstance(surface_id, str):
                rows.setdefault(surface_id, []).append(witness)
    return rows


def _exploit_rows_by_surface(exploit_report: dict[str, Any] | None) -> dict[str, list[dict[str, Any]]]:
    rows: dict[str, list[dict[str, Any]]] = {}
    if not exploit_report:
        return rows
    for witness in exploit_report.get("top_witnesses", []):
        if not isinstance(witness, dict):
            continue
        for surface_id in witness.get("surface_ids", []):
            if isinstance(surface_id, str):
                rows.setdefault(surface_id, []).append(witness)
    return rows


def _atlas_by_surface(atlas: dict[str, Any] | None) -> dict[str, dict[str, Any]]:
    if not atlas:
        return {}
    return {
        str(entry["surface_id"]): entry
        for entry in atlas.get("entries", [])
        if isinstance(entry, dict) and isinstance(entry.get("surface_id"), str)
    }


def _run_shape_validation(*, python_bin: str) -> dict[str, Any]:
    commands = [
        [python_bin, "tools/shapeforge_validate.py", str(DEFAULT_WORLD_MODEL)],
        [python_bin, "tools/check_shape_v1_ratchet.py"],
    ]
    results: list[dict[str, Any]] = []
    ok = True
    for command in commands:
        proc = subprocess.run(command, cwd=REPO_ROOT, check=False, capture_output=True, text=True)
        row = {
            "command": command,
            "returncode": proc.returncode,
            "ok": proc.returncode == 0,
            "stdout": proc.stdout,
            "stderr": proc.stderr,
        }
        results.append(row)
        ok = ok and bool(row["ok"])
    return {"ran": True, "ok": ok, "commands": commands, "results": results}


def _top_exploit_row(rows: list[dict[str, Any]]) -> dict[str, Any] | None:
    if not rows:
        return None
    return max(
        rows,
        key=lambda row: (
            int(row.get("proximity_score", 0) or 0),
            SEVERITY_ORDER.get(str(row.get("severity_band", "unknown")), -1),
            str(row.get("witness_id") or ""),
        ),
    )


def build_shapeforge_promotion_bridge_report(
    *,
    campaign_report: str | Path,
    target_manifest: str | Path | None = None,
    run_shapeforge_checks: bool = False,
    python_bin: str | None = None,
) -> dict[str, Any]:
    campaign_report_path = _resolve_path(campaign_report)
    if campaign_report_path is None or not campaign_report_path.is_file():
        raise ValueError(f"missing campaign report: {campaign_report}")
    report = _load_json(campaign_report_path)
    errors: list[str] = []
    if report.get("schema") != "zenodex/acceptance-tcb-fuzz-campaign-report/v1":
        errors.append("campaign report schema must equal zenodex/acceptance-tcb-fuzz-campaign-report/v1")
    if report.get("plan_only") is True:
        errors.append("campaign report is plan-only; promotion bridge requires executed artifacts")

    raw_artifacts = report.get("artifacts")
    artifacts: dict[str, Any] = raw_artifacts if isinstance(raw_artifacts, dict) else {}
    manifest_value = artifacts.get("target_manifest")
    manifest_raw = target_manifest or (manifest_value if isinstance(manifest_value, str) else DEFAULT_TARGET_MANIFEST)
    manifest_path = _resolve_path(manifest_raw)
    if manifest_path is None or not manifest_path.is_file():
        errors.append(f"missing dangerous-surface manifest: {manifest_raw}")
        surfaces: dict[str, DangerousSurface] = {}
    else:
        surfaces = _surfaces_by_id(manifest_path)

    introspection = _load_artifact(
        report,
        campaign_report_path,
        "introspection_out",
        "zenodex/acceptance-tcb-fuzz-introspection/v1",
        errors,
    )
    atlas = _load_artifact(
        report,
        campaign_report_path,
        "atlas_out",
        "zenodex/acceptance-tcb-weird-machine-atlas/v1",
        errors,
    )
    suggestions = _load_artifact(
        report,
        campaign_report_path,
        "surface_suggestions_out",
        "zenodex/acceptance-tcb-surface-suggestions/v1",
        errors,
    )
    guard_report = _load_artifact(
        report,
        campaign_report_path,
        "guard_attribution_out",
        "zenodex/acceptance-tcb-guard-attribution/v1",
        errors,
    )
    exploit_report = _load_artifact(
        report,
        campaign_report_path,
        "exploit_proximity_out",
        "zenodex/acceptance-tcb-exploit-proximity/v1",
        errors,
    )

    guard_by_surface = _guard_rows_by_surface(guard_report)
    exploit_by_surface = _exploit_rows_by_surface(exploit_report)
    atlas_entries = _atlas_by_surface(atlas)
    candidate_deltas: list[dict[str, Any]] = []
    blocked_surfaces: list[dict[str, Any]] = []

    if introspection is not None:
        for row in introspection.get("surfaces", []):
            if not isinstance(row, dict):
                continue
            surface_id = row.get("surface_id")
            if not isinstance(surface_id, str) or surface_id not in surfaces:
                errors.append(f"introspection surface {surface_id!r} is not declared in the manifest")
                continue
            surface = surfaces[surface_id]
            status = row.get("status")
            if status not in {"witnessed", "reached_no_witness", "harnessed_unreached", "unharnessed"}:
                errors.append(f"surface {surface_id} has unsupported status {status!r}")
                continue
            guards = guard_by_surface.get(surface_id, [])
            exploits = exploit_by_surface.get(surface_id, [])
            top_exploit = _top_exploit_row(exploits)
            axis = _surface_axis(surface)
            if status in {"witnessed", "reached_no_witness"}:
                candidate_deltas.append(
                    {
                        "delta_id": f"stateful_surface:{surface_id}",
                        "kind": "shapeforge_scenario_candidate",
                        "surface_id": surface_id,
                        "machine_family": surface.machine_family,
                        "axis": axis,
                        "improvement_target": _improvement_target(surface, axis),
                        "evidence_class": MAX_SCENARIO_EVIDENCE,
                        "status": "candidate_only",
                        "status_if_unproved": "blocked_for_settlement_authority",
                        "invariant_boundary": surface.invariant_boundary,
                        "action_grammar": surface.action_grammar,
                        "candidate_scenario": {
                            "scenario_id": f"stateful_{surface_id}",
                            "axis": axis,
                            "perturbation": f"Replay {surface.action_grammar} against {surface.invariant_boundary}.",
                            "expected_effects": [
                                "The boundary rejects before runtime mutation.",
                                "Any surviving state remains research-only until promoted by a stronger proof gate.",
                            ],
                            "improvement_target": _improvement_target(surface, axis),
                            "evidence_required": [MAX_SCENARIO_EVIDENCE],
                        },
                        "evidence_sources": {
                            "campaign_report": _relpath(campaign_report_path),
                            "introspection": introspection.get("_artifact_path"),
                            "atlas": None if atlas is None else atlas.get("_artifact_path"),
                            "surface_suggestions": None if suggestions is None else suggestions.get("_artifact_path"),
                            "guard_attribution": None if guard_report is None else guard_report.get("_artifact_path"),
                            "exploit_proximity": None if exploit_report is None else exploit_report.get("_artifact_path"),
                            "witness_ids": sorted(set(row.get("witness_ids", []))),
                            "guard_families": sorted({str(guard.get("guard_family")) for guard in guards if guard.get("guard_family")}),
                            "top_exploit_witness_ids": [str(exploit.get("witness_id")) for exploit in exploits[:3] if exploit.get("witness_id")],
                            "exploit_proximity": {
                                "max_severity_band": None if top_exploit is None else top_exploit.get("severity_band"),
                                "max_proximity_score": 0 if top_exploit is None else int(top_exploit.get("proximity_score", 0) or 0),
                                "flags": {} if top_exploit is None else top_exploit.get("flags", {}),
                            },
                            "atlas_witness_status": atlas_entries.get(surface_id, {}).get("witness_status"),
                        },
                        "promotion_blockers": [
                            "Do not upgrade above tested_discovery without Lean/Tau/ESSO proof or a checked certificate.",
                            "Do not authorize settlement from this bridge; only FIRE-V/runtime verifier receipts may authorize deltas.",
                        ],
                    }
                )
            else:
                blocked_surfaces.append(
                    {
                        "surface_id": surface_id,
                        "machine_family": surface.machine_family,
                        "status": status,
                        "reason": "no replayable reached state or minimized witness in campaign artifacts",
                    }
                )

    shape_validation = {
        "ran": False,
        "ok": None,
        "commands": [
            ["python3", "tools/shapeforge_validate.py", _relpath(DEFAULT_WORLD_MODEL)],
            ["python3", "tools/check_shape_v1_ratchet.py"],
        ],
        "promotion_gate": "blocked_until_run" if not run_shapeforge_checks else "required",
    }
    if run_shapeforge_checks:
        shape_validation = _run_shape_validation(python_bin=python_bin or sys.executable)
        if not shape_validation["ok"]:
            errors.append("ShapeForge validation command failed")

    return {
        "schema": SHAPEFORGE_BRIDGE_SCHEMA,
        "ok": not errors,
        "generated_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "errors": errors,
        "source_campaign_report": _relpath(campaign_report_path),
        "target_manifest": None if manifest_path is None else _relpath(manifest_path),
        "evidence_class_ceiling": MAX_SCENARIO_EVIDENCE,
        "promotion_policy": {
            "candidate_only": True,
            "safe_states_researchable_only": True,
            "requires_replayable_artifacts": True,
            "max_evidence_class": MAX_SCENARIO_EVIDENCE,
        },
        "shape_validation": shape_validation,
        "candidate_count": len(candidate_deltas),
        "blocked_count": len(blocked_surfaces),
        "candidate_deltas": sorted(candidate_deltas, key=lambda row: row["delta_id"]),
        "blocked_surfaces": sorted(blocked_surfaces, key=lambda row: row["surface_id"]),
    }


def _load_bridge_report(bridge_report: str | Path | dict[str, Any]) -> dict[str, Any]:
    if isinstance(bridge_report, dict):
        return bridge_report
    path = _resolve_path(bridge_report)
    if path is None or not path.is_file():
        raise ValueError(f"missing bridge report: {bridge_report}")
    return _load_json(path)


def _severity_at_least(value: str | None, threshold: str) -> bool:
    return SEVERITY_ORDER.get(str(value or "unknown"), -1) >= SEVERITY_ORDER[threshold]


def build_minimal_witness_language_audit(
    *,
    surface_ids: list[str] | None = None,
) -> dict[str, Any]:
    selected = list(surface_ids) if surface_ids is not None else list(CRITICAL_DISASTER_SURFACE_IDS)
    errors: list[str] = []
    rows: list[dict[str, Any]] = []
    for surface_id in selected:
        template = SURFACE_WITNESS_LANGUAGE_REQUIREMENTS.get(surface_id)
        if template is None:
            errors.append(f"{surface_id}: missing witness-language requirements")
            continue
        fields = [str(item) for item in template.get("required_binding_fields", []) if isinstance(item, str)]
        reject_tokens = [str(item) for item in template.get("reject_ambiguity_tokens", []) if isinstance(item, str)]
        if not fields:
            errors.append(f"{surface_id}: required_binding_fields must be non-empty")
        if not reject_tokens:
            errors.append(f"{surface_id}: reject_ambiguity_tokens must be non-empty")
        rows.append(
            {
                "surface_id": surface_id,
                "language": template.get("language"),
                "target": "Good(x) <-> exists z Proves_L(z, x)",
                "claim_tier": "bounded_witness_language",
                "required_binding_fields": fields,
                "reject_ambiguity_tokens": reject_tokens,
                "rejects_ambiguous_witnesses": bool(fields and reject_tokens),
            }
        )
    return {
        "schema": MINIMAL_WITNESS_LANGUAGE_AUDIT_SCHEMA,
        "ok": not errors,
        "generated_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "errors": errors,
        "surface_count": len(rows),
        "surfaces": sorted(rows, key=lambda row: str(row["surface_id"])),
    }


def build_cross_surface_witness_exploration_plan(
    *,
    pair_ids: list[str] | None = None,
) -> dict[str, Any]:
    selected_pair_ids = set(pair_ids) if pair_ids is not None else None
    errors: list[str] = []
    pairs: list[dict[str, Any]] = []
    audit = build_minimal_witness_language_audit()
    if audit.get("ok") is not True:
        errors.extend(str(error) for error in audit.get("errors", []))
    known_surfaces = {str(row["surface_id"]) for row in audit.get("surfaces", []) if isinstance(row, dict)}
    for pair in CROSS_SURFACE_WITNESS_PAIRS:
        pair_id = str(pair.get("pair_id"))
        if selected_pair_ids is not None and pair_id not in selected_pair_ids:
            continue
        surface_ids = [str(item) for item in pair.get("surface_ids", ()) if isinstance(item, str)]
        missing_surfaces = [surface_id for surface_id in surface_ids if surface_id not in known_surfaces]
        commands = pair.get("commands", [])
        if missing_surfaces:
            errors.append(f"{pair_id}: missing witness-language audit surface(s): {', '.join(missing_surfaces)}")
        if not isinstance(commands, list) or not commands:
            errors.append(f"{pair_id}: commands must be a non-empty list")
            commands = []
        for command in commands:
            if not isinstance(command, list) or not all(isinstance(item, str) for item in command):
                errors.append(f"{pair_id}: command entries must be lists of strings")
        pairs.append(
            {
                "pair_id": pair_id,
                "surface_ids": surface_ids,
                "bounds": pair.get("bounds", {}),
                "commands": commands,
                "evidence_class_ceiling": MAX_SCENARIO_EVIDENCE,
                "status": "bounded_exploration_required",
            }
        )
    if not pairs:
        errors.append("no cross-surface witness pairs selected")
    return {
        "schema": CROSS_SURFACE_WITNESS_EXPLORATION_SCHEMA,
        "ok": not errors,
        "generated_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "errors": errors,
        "pair_count": len(pairs),
        "witness_language_audit": audit,
        "pairs": sorted(pairs, key=lambda row: str(row["pair_id"])),
    }


def build_disaster_search_expansion_plan(
    *,
    axis_ids: list[str] | None = None,
    target_manifest: str | Path | None = None,
) -> dict[str, Any]:
    selected_axis_ids = set(axis_ids) if axis_ids is not None else None
    manifest_path = _resolve_path(target_manifest or DEFAULT_TARGET_MANIFEST)
    errors: list[str] = []
    if manifest_path is None or not manifest_path.is_file():
        errors.append(f"missing dangerous-surface manifest: {target_manifest or DEFAULT_TARGET_MANIFEST}")
        surfaces: dict[str, DangerousSurface] = {}
    else:
        surfaces = _surfaces_by_id(manifest_path)

    axes: list[dict[str, Any]] = []
    for axis in DISASTER_SEARCH_EXPANSION_AXES:
        axis_id = str(axis.get("axis_id"))
        if selected_axis_ids is not None and axis_id not in selected_axis_ids:
            continue
        surface_ids = [str(item) for item in axis.get("surface_ids", ()) if isinstance(item, str)]
        missing_surface_ids = [surface_id for surface_id in surface_ids if surface_id not in surfaces]
        if missing_surface_ids:
            errors.append(f"{axis_id}: undeclared surface id(s): {', '.join(missing_surface_ids)}")
        commands = [list(command) for command in axis.get("commands", ()) if isinstance(command, tuple)]
        if not commands:
            errors.append(f"{axis_id}: commands must be non-empty")
        for command in commands:
            if not all(isinstance(item, str) and item for item in command):
                errors.append(f"{axis_id}: command entries must be non-empty strings")
        axes.append(
            {
                "axis_id": axis_id,
                "priority_score": int(axis.get("priority_score", 0) or 0),
                "surface_ids": surface_ids,
                "what_if": str(axis.get("what_if") or ""),
                "disaster_state_template": str(axis.get("disaster_state_template") or ""),
                "mutation_families": [str(item) for item in axis.get("mutation_families", ()) if isinstance(item, str)],
                "bounded_harness_ideas": [str(item) for item in axis.get("bounded_harness_ideas", ()) if isinstance(item, str)],
                "commands": commands,
                "evidence_class_ceiling": MAX_SCENARIO_EVIDENCE,
                "claim_tier": "candidate_generation_only",
                "status": "not_exhausted",
            }
        )
    if not axes:
        errors.append("no disaster search expansion axes selected")

    axes_sorted = sorted(axes, key=lambda row: (-int(row["priority_score"]), str(row["axis_id"])))
    return {
        "schema": DISASTER_SEARCH_EXPANSION_PLAN_SCHEMA,
        "ok": not errors,
        "generated_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "errors": errors,
        "axis_count": len(axes_sorted),
        "policy": {
            "evidence_class_ceiling": MAX_SCENARIO_EVIDENCE,
            "readme_exhaustive_claim": "defer",
            "reason": "additional what-if axes remain useful search work, so coverage is closed only relative to current declared obligations",
        },
        "axes": axes_sorted,
    }


def _risk_counts(candidates: list[dict[str, Any]]) -> dict[str, int]:
    counts = {key: 0 for key in ("unknown", "low", "medium", "high", "critical")}
    for candidate in candidates:
        evidence_sources = candidate.get("evidence_sources", {})
        if not isinstance(evidence_sources, dict):
            counts["unknown"] += 1
            continue
        proximity = evidence_sources.get("exploit_proximity", {})
        if not isinstance(proximity, dict):
            counts["unknown"] += 1
            continue
        band = str(proximity.get("max_severity_band") or "unknown")
        if band not in counts:
            band = "unknown"
        counts[band] += 1
    return counts


def _ledger_record_for_candidate(candidate: dict[str, Any]) -> dict[str, Any]:
    evidence_sources = candidate.get("evidence_sources", {})
    if not isinstance(evidence_sources, dict):
        evidence_sources = {}
    witness_ids = [str(row) for row in evidence_sources.get("witness_ids", []) if isinstance(row, str)]
    guard_families = [str(row) for row in evidence_sources.get("guard_families", []) if isinstance(row, str)]
    proximity = evidence_sources.get("exploit_proximity", {})
    if not isinstance(proximity, dict):
        proximity = {}
    if witness_ids and guard_families:
        reachability_status = "blocked_by_guard_witness"
    elif witness_ids:
        reachability_status = "witnessed_without_guard_attribution"
    else:
        reachability_status = "reached_without_minimized_witness"
    return {
        "record_id": f"blocked_state:{candidate.get('surface_id')}",
        "surface_id": candidate.get("surface_id"),
        "machine_family": candidate.get("machine_family"),
        "negative_kind": "blocked_promotion",
        "claim": f"Attempted disaster state for {candidate.get('surface_id')} remains research-only until replay and proof obligations close.",
        "reachability_status": reachability_status,
        "current_evidence_class": candidate.get("evidence_class"),
        "target_evidence_class": "contract_or_proved",
        "guard_families": guard_families,
        "witness_ids": witness_ids,
        "severity_band": proximity.get("max_severity_band") or "unknown",
        "proximity_score": int(proximity.get("max_proximity_score", 0) or 0),
        "replay_pointer": evidence_sources.get("campaign_report"),
    }


def build_disaster_reachability_ratchet_report(
    *,
    bridge_report: str | Path | dict[str, Any],
    require_shape_validation: bool = False,
    max_blocked_surfaces: int = 0,
    require_witnesses: bool = True,
    require_guard_attribution: bool = False,
    high_severity_requires_witness: str = "high",
) -> dict[str, Any]:
    bridge = _load_bridge_report(bridge_report)
    errors: list[str] = []
    warnings: list[str] = []

    if bridge.get("schema") != SHAPEFORGE_BRIDGE_SCHEMA:
        errors.append(f"bridge report schema must equal {SHAPEFORGE_BRIDGE_SCHEMA}")
    if bridge.get("ok") is not True:
        errors.append("bridge report is not ok")
    if bridge.get("evidence_class_ceiling") != MAX_SCENARIO_EVIDENCE:
        errors.append("bridge evidence_class_ceiling must remain tested_discovery")
    policy = bridge.get("promotion_policy")
    if not isinstance(policy, dict) or policy.get("candidate_only") is not True:
        errors.append("bridge promotion policy must be candidate_only")
    if not isinstance(policy, dict) or policy.get("safe_states_researchable_only") is not True:
        errors.append("bridge promotion policy must mark safe_states_researchable_only")

    shape_validation = bridge.get("shape_validation")
    if require_shape_validation:
        if not isinstance(shape_validation, dict) or shape_validation.get("ran") is not True:
            errors.append("shape validation must be run for this ratchet")
        elif shape_validation.get("ok") is not True:
            errors.append("shape validation failed")

    blocked_surfaces = bridge.get("blocked_surfaces", [])
    if not isinstance(blocked_surfaces, list):
        errors.append("blocked_surfaces must be a list")
        blocked_surfaces = []
    if len(blocked_surfaces) > max_blocked_surfaces:
        errors.append(f"blocked surface count {len(blocked_surfaces)} exceeds budget {max_blocked_surfaces}")

    candidates = bridge.get("candidate_deltas", [])
    if not isinstance(candidates, list):
        errors.append("candidate_deltas must be a list")
        candidates = []
    if not candidates:
        errors.append("ratchet requires at least one candidate delta")

    ledger_records: list[dict[str, Any]] = []
    for candidate in candidates:
        if not isinstance(candidate, dict):
            errors.append("candidate_deltas entries must be objects")
            continue
        surface_id = str(candidate.get("surface_id") or "<unknown>")
        if candidate.get("evidence_class") != MAX_SCENARIO_EVIDENCE:
            errors.append(f"{surface_id}: evidence_class must remain tested_discovery")
        if candidate.get("status") != "candidate_only":
            errors.append(f"{surface_id}: status must remain candidate_only")
        evidence_sources = candidate.get("evidence_sources", {})
        if not isinstance(evidence_sources, dict):
            errors.append(f"{surface_id}: evidence_sources must be an object")
            continue
        witness_ids = [row for row in evidence_sources.get("witness_ids", []) if isinstance(row, str)]
        guard_families = [row for row in evidence_sources.get("guard_families", []) if isinstance(row, str)]
        proximity = evidence_sources.get("exploit_proximity", {})
        if not isinstance(proximity, dict):
            proximity = {}
        severity = str(proximity.get("max_severity_band") or "unknown")
        if require_witnesses and not witness_ids:
            errors.append(f"{surface_id}: missing minimized witness ids")
        if require_guard_attribution and not guard_families:
            errors.append(f"{surface_id}: missing guard attribution")
        if _severity_at_least(severity, high_severity_requires_witness) and not witness_ids:
            errors.append(f"{surface_id}: {severity} severity candidate lacks a minimized witness")
        if not guard_families:
            warnings.append(f"{surface_id}: no guard attribution available")
        ledger_records.append(_ledger_record_for_candidate(candidate))

    return {
        "schema": DISASTER_REACHABILITY_RATCHET_SCHEMA,
        "ok": not errors,
        "generated_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "errors": errors,
        "warnings": warnings,
        "source_bridge_report": bridge.get("source_campaign_report"),
        "policy": {
            "max_blocked_surfaces": max_blocked_surfaces,
            "require_shape_validation": require_shape_validation,
            "require_witnesses": require_witnesses,
            "require_guard_attribution": require_guard_attribution,
            "high_severity_requires_witness": high_severity_requires_witness,
            "evidence_class_ceiling": MAX_SCENARIO_EVIDENCE,
        },
        "surface_count": len(candidates) + len(blocked_surfaces),
        "candidate_count": len(candidates),
        "blocked_count": len(blocked_surfaces),
        "risk_counts": _risk_counts(candidates),
        "blocked_surfaces": blocked_surfaces,
        "negative_knowledge_candidates": sorted(ledger_records, key=lambda row: str(row["record_id"])),
    }


def run_scenario_candidate(
    *,
    candidate: dict[str, Any],
    target_manifest: str | Path = DEFAULT_TARGET_MANIFEST,
    execute: bool = False,
    report_out: str | Path | None = None,
    campaign_root: str | Path | None = None,
    timestamp_utc: str | None = None,
    run_id: str | None = None,
    build_bridge: bool = True,
    run_shapeforge_checks: bool = False,
    python_bin: str | None = None,
) -> dict[str, Any]:
    check = check_scenario_candidate(candidate, target_manifest=target_manifest)
    command = list(check.get("replay_plan", {}).get("command", []))
    if report_out is not None:
        command.extend(["--report-out", str(report_out)])
    if campaign_root is not None:
        command.extend(["--campaign-root", str(campaign_root)])
    if timestamp_utc is not None:
        command.extend(["--timestamp-utc", timestamp_utc])
    if run_id is not None:
        command.extend(["--run-id", run_id])

    receipt: dict[str, Any] = {
        "schema": SCENARIO_RUN_RECEIPT_SCHEMA,
        "ok": bool(check["ok"]) and not execute,
        "plan_only": not execute,
        "generated_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "candidate_check": check,
        "command": command,
        "campaign_result": None,
        "bridge_report": None,
    }
    if not check["ok"]:
        receipt["ok"] = False
        return receipt
    if not execute:
        return receipt

    proc = subprocess.run(command, cwd=REPO_ROOT, check=False, capture_output=True, text=True)
    campaign_payload: dict[str, Any] | None = None
    if proc.stdout.strip():
        try:
            parsed = json.loads(proc.stdout)
            if isinstance(parsed, dict):
                campaign_payload = parsed
        except json.JSONDecodeError:
            campaign_payload = None
    receipt["campaign_result"] = {
        "returncode": proc.returncode,
        "ok": proc.returncode == 0,
        "stdout": proc.stdout,
        "stderr": proc.stderr,
        "report_out": None if campaign_payload is None else campaign_payload.get("report_out"),
    }
    if proc.returncode != 0:
        receipt["ok"] = False
        return receipt

    if build_bridge:
        campaign_report_path = None
        if campaign_payload is not None and isinstance(campaign_payload.get("report_out"), str):
            campaign_report_path = campaign_payload["report_out"]
        elif report_out is not None:
            campaign_report_path = str(report_out)
        if campaign_report_path:
            receipt["bridge_report"] = build_shapeforge_promotion_bridge_report(
                campaign_report=campaign_report_path,
                target_manifest=target_manifest,
                run_shapeforge_checks=run_shapeforge_checks,
                python_bin=python_bin,
            )
    receipt["ok"] = bool(receipt["campaign_result"]["ok"]) and (
        receipt["bridge_report"] is None or bool(receipt["bridge_report"].get("ok"))
    )
    return receipt


def _load_ratchet_report(ratchet_report: str | Path | dict[str, Any]) -> dict[str, Any]:
    if isinstance(ratchet_report, dict):
        return ratchet_report
    path = _resolve_path(ratchet_report)
    if path is None or not path.is_file():
        raise ValueError(f"missing ratchet report: {ratchet_report}")
    return _load_json(path)


def _artifact_status(artifacts: list[str]) -> tuple[list[str], list[str]]:
    present: list[str] = []
    missing: list[str] = []
    for artifact in artifacts:
        path = _resolve_path(artifact)
        if path is not None and path.exists():
            present.append(artifact)
        else:
            missing.append(artifact)
    return present, missing


def _lane_with_status(lane: dict[str, Any]) -> dict[str, Any]:
    artifacts = [str(artifact) for artifact in lane.get("artifacts", [])]
    present, missing = _artifact_status(artifacts)
    out = {
        "kind": lane.get("kind"),
        "name": lane.get("name"),
        "artifacts": artifacts,
        "commands": lane.get("commands", []),
        "present_artifacts": present,
        "missing_artifacts": missing,
        "artifact_status": "present" if not missing else "missing",
    }
    return out


def build_stateful_disaster_proof_obligation_packet(
    *,
    ratchet_report: str | Path | dict[str, Any],
    min_severity: str = "high",
    include_unknown: bool = False,
    require_formal_lane: bool = True,
) -> dict[str, Any]:
    ratchet = _load_ratchet_report(ratchet_report)
    errors: list[str] = []
    warnings: list[str] = []
    if ratchet.get("schema") != DISASTER_REACHABILITY_RATCHET_SCHEMA:
        errors.append(f"ratchet report schema must equal {DISASTER_REACHABILITY_RATCHET_SCHEMA}")
    if ratchet.get("ok") is not True:
        errors.append("ratchet report is not ok")

    rows = ratchet.get("negative_knowledge_candidates", [])
    if not isinstance(rows, list):
        errors.append("negative_knowledge_candidates must be a list")
        rows = []

    obligations: list[dict[str, Any]] = []
    classification_gaps: list[dict[str, Any]] = []
    for row in rows:
        if not isinstance(row, dict):
            errors.append("negative_knowledge_candidates entries must be objects")
            continue
        surface_id = str(row.get("surface_id") or "")
        severity = str(row.get("severity_band") or "unknown")
        if severity == "unknown":
            if include_unknown:
                classification_gaps.append(
                    {
                        "surface_id": surface_id,
                        "reason": "exploit proximity severity is unknown; run or enrich exploit proximity before formal promotion",
                        "witness_ids": row.get("witness_ids", []),
                    }
                )
            continue
        if not _severity_at_least(severity, min_severity):
            continue

        template = SURFACE_FORMAL_LANES.get(surface_id)
        if template is None:
            errors.append(f"{surface_id}: no formal lane mapping for {severity} disaster surface")
            continue
        lanes = [_lane_with_status(lane) for lane in template["lanes"]]
        missing_artifacts = sorted({artifact for lane in lanes for artifact in lane["missing_artifacts"]})
        formal_lane_count = sum(1 for lane in lanes if lane.get("kind") in FORMAL_LANE_KINDS)
        if missing_artifacts:
            errors.append(f"{surface_id}: missing proof-lane artifact(s): {', '.join(missing_artifacts)}")
        if require_formal_lane and formal_lane_count == 0:
            errors.append(f"{surface_id}: no formal closure lane declared")
        witness_ids = [str(item) for item in row.get("witness_ids", []) if isinstance(item, str)]
        if not witness_ids:
            errors.append(f"{surface_id}: proof obligation has no replay witness ids")
        obligations.append(
            {
                "obligation_id": f"proof_obligation:{surface_id}",
                "surface_id": surface_id,
                "machine_family": row.get("machine_family"),
                "severity_band": severity,
                "proximity_score": int(row.get("proximity_score", 0) or 0),
                "current_evidence_class": row.get("current_evidence_class"),
                "target_evidence_class": template["target_evidence_class"],
                "obligation": template["obligation"],
                "witness_ids": witness_ids,
                "guard_families": row.get("guard_families", []),
                "replay_pointer": row.get("replay_pointer"),
                "formal_lane_count": formal_lane_count,
                "lanes": lanes,
                "promotion_status": "blocked_until_formal_closure",
            }
        )

    if not obligations:
        warnings.append("no obligations selected under the current severity filter")

    return {
        "schema": PROOF_OBLIGATION_PACKET_SCHEMA,
        "ok": not errors,
        "generated_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "errors": errors,
        "warnings": warnings,
        "source_ratchet_report": ratchet.get("source_bridge_report"),
        "policy": {
            "min_severity": min_severity,
            "include_unknown": include_unknown,
            "require_formal_lane": require_formal_lane,
            "promotion_status": "blocked_until_formal_closure",
        },
        "obligation_count": len(obligations),
        "classification_gap_count": len(classification_gaps),
        "obligations": sorted(obligations, key=lambda item: str(item["obligation_id"])),
        "classification_gaps": sorted(classification_gaps, key=lambda item: str(item["surface_id"])),
    }


def _load_proof_obligation_packet(packet: str | Path | dict[str, Any]) -> dict[str, Any]:
    if isinstance(packet, dict):
        return packet
    path = _resolve_path(packet)
    if path is None or not path.is_file():
        raise ValueError(f"missing proof-obligation packet: {packet}")
    return _load_json(path)


def _selected_obligations(
    packet: dict[str, Any],
    *,
    surface_ids: set[str] | None,
) -> list[dict[str, Any]]:
    rows = packet.get("obligations", [])
    if not isinstance(rows, list):
        return []
    selected: list[dict[str, Any]] = []
    for row in rows:
        if not isinstance(row, dict):
            continue
        surface_id = str(row.get("surface_id") or "")
        if surface_ids is not None and surface_id not in surface_ids:
            continue
        selected.append(row)
    return selected


def _command_status(*, returncode: int, stdout: str, stderr: str) -> str:
    combined = f"{stdout}\n{stderr}".lower()
    if returncode != 0:
        return "failed"
    if " skipped" in combined or "skipped," in combined or "skipped in " in combined:
        return "inconclusive"
    return "passed"


def _run_obligation_command(command: list[str], *, timeout_s: int) -> dict[str, Any]:
    started = time.monotonic()
    try:
        proc = subprocess.run(
            command,
            cwd=REPO_ROOT,
            check=False,
            capture_output=True,
            text=True,
            timeout=timeout_s,
        )
        duration_s = round(time.monotonic() - started, 3)
        status = _command_status(returncode=proc.returncode, stdout=proc.stdout, stderr=proc.stderr)
        return {
            "command": command,
            "status": status,
            "ok": status == "passed",
            "returncode": proc.returncode,
            "duration_s": duration_s,
            "stdout": proc.stdout,
            "stderr": proc.stderr,
        }
    except subprocess.TimeoutExpired as exc:
        stdout = exc.stdout.decode("utf-8", errors="replace") if isinstance(exc.stdout, bytes) else (exc.stdout or "")
        stderr = exc.stderr.decode("utf-8", errors="replace") if isinstance(exc.stderr, bytes) else (exc.stderr or "")
        return {
            "command": command,
            "status": "inconclusive",
            "ok": False,
            "returncode": None,
            "duration_s": round(time.monotonic() - started, 3),
            "stdout": stdout,
            "stderr": stderr + f"\ntimeout after {timeout_s}s",
        }


def _pytest_group_key(command: list[str]) -> tuple[str | None, tuple[str, ...]] | None:
    if not command or command[0] != "pytest":
        return None
    args = list(command[1:])
    if args and args[0] == "-q":
        args = args[1:]

    k_expr: str | None = None
    paths: list[str] = []
    idx = 0
    while idx < len(args):
        arg = args[idx]
        if arg == "-k":
            if k_expr is not None or idx + 1 >= len(args):
                return None
            k_expr = args[idx + 1]
            idx += 2
            continue
        if arg.startswith("-"):
            return None
        paths.append(arg)
        idx += 1
    if not paths:
        return None
    return k_expr, tuple(paths)


def _parse_aggregate_pytest_axes(
    raw_axes: list[Any],
    selected_axis_ids: set[str] | None,
) -> tuple[list[_AxisPytestCommands], list[_PytestShardKey]] | None:
    axis_commands: list[_AxisPytestCommands] = []
    shard_keys: set[_PytestShardKey] = set()
    for axis in raw_axes:
        if not isinstance(axis, dict):
            return None
        axis_id = str(axis.get("axis_id") or "")
        if selected_axis_ids is not None and axis_id not in selected_axis_ids:
            continue
        raw_commands = axis.get("commands", [])
        if not isinstance(raw_commands, list) or not raw_commands:
            return None

        parsed_commands: list[_ParsedPytestCommand] = []
        for command in raw_commands:
            if not isinstance(command, list) or not all(isinstance(item, str) for item in command):
                return None
            parsed = _pytest_group_key(command)
            if parsed is None:
                return None
            k_expr, paths = parsed
            command_shards = tuple((k_expr, path) for path in paths)
            shard_keys.update(command_shards)
            parsed_commands.append((command, command_shards))
        axis_commands.append((axis, parsed_commands))

    if not axis_commands:
        return None
    ordered_shard_keys = sorted(
        shard_keys,
        key=lambda key: ("" if key[0] is None else str(key[0]), key[1]),
    )
    return axis_commands, ordered_shard_keys


def _run_aggregate_pytest_shards(
    ordered_shard_keys: list[_PytestShardKey],
    *,
    timeout_s: int,
) -> tuple[list[dict[str, Any]], dict[_PytestShardKey, dict[str, Any]]]:
    component_id_by_shard = {
        shard_key: f"pytest-component-{component_index:03d}"
        for component_index, shard_key in enumerate(ordered_shard_keys)
    }

    def run_component(shard_key: _PytestShardKey) -> dict[str, Any]:
        k_expr, path = shard_key
        command = [sys.executable, "-m", "pytest", "-q"]
        if k_expr is not None:
            command.extend(["-k", k_expr])
        command.append(path)
        result = _run_obligation_command(command, timeout_s=timeout_s)
        result["aggregate_pytest_group"] = {
            "component_id": component_id_by_shard[shard_key],
            "k_expr": k_expr,
            "path_count": 1,
        }
        return result

    worker_count = min(MAX_AGGREGATE_PYTEST_WORKERS, len(ordered_shard_keys))
    with ThreadPoolExecutor(max_workers=worker_count) as executor:
        aggregate_results = list(executor.map(run_component, ordered_shard_keys))
    return (
        aggregate_results,
        dict(zip(ordered_shard_keys, aggregate_results, strict=True)),
    )


def _aggregate_pytest_command_result(
    command: list[str],
    command_shards: tuple[_PytestShardKey, ...],
    aggregate_results_by_shard: dict[_PytestShardKey, dict[str, Any]],
) -> dict[str, Any]:
    aggregates = [aggregate_results_by_shard[shard] for shard in command_shards]
    statuses = {str(aggregate.get("status")) for aggregate in aggregates}
    if "failed" in statuses:
        status = "failed"
    elif "inconclusive" in statuses:
        status = "inconclusive"
    else:
        status = "passed"
    returncodes = [aggregate.get("returncode") for aggregate in aggregates]
    returncode = next((code for code in returncodes if code not in {0, None}), None)
    if status == "passed":
        returncode = 0
    return {
        "command": command,
        "status": status,
        "ok": status == "passed",
        "returncode": returncode,
        "duration_s": round(
            sum(float(aggregate.get("duration_s", 0.0)) for aggregate in aggregates),
            3,
        ),
        "stdout": "",
        "stderr": "",
        "covered_by_aggregate_pytest": True,
        "aggregate_commands": [aggregate.get("command") for aggregate in aggregates],
        "aggregate_pytest_groups": [
            aggregate.get("aggregate_pytest_group") for aggregate in aggregates
        ],
    }


def _run_aggregate_pytest_axes(
    raw_axes: list[Any],
    *,
    selected_axis_ids: set[str] | None,
    timeout_s: int,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]] | None:
    parsed = _parse_aggregate_pytest_axes(raw_axes, selected_axis_ids)
    if parsed is None:
        return None
    axis_commands, ordered_shard_keys = parsed

    # Run one shard per exact test path and -k expression.  Commands that name
    # the same path share one result, while a slow or failing path cannot spend
    # the evidence budget of an unrelated axis.  An original multi-path
    # command closes only when every one of its shards passes.
    aggregate_results, aggregate_results_by_shard = _run_aggregate_pytest_shards(
        ordered_shard_keys,
        timeout_s=timeout_s,
    )

    axis_results: list[dict[str, Any]] = []
    for axis, parsed_commands in axis_commands:
        command_results: list[dict[str, Any]] = []
        command_statuses: set[str] = set()
        for command, command_shards in parsed_commands:
            command_result = _aggregate_pytest_command_result(
                command,
                command_shards,
                aggregate_results_by_shard,
            )
            command_statuses.add(str(command_result["status"]))
            command_results.append(command_result)
        if "failed" in command_statuses:
            axis_status = "found_or_regressed"
        elif "inconclusive" in command_statuses:
            axis_status = "inconclusive"
        else:
            axis_status = "unreachable_under_current_bounds"
        axis_results.append(
            {
                "axis_id": str(axis.get("axis_id") or ""),
                "priority_score": int(axis.get("priority_score", 0) or 0),
                "surface_ids": axis.get("surface_ids", []),
                "what_if": axis.get("what_if"),
                "disaster_state_template": axis.get("disaster_state_template"),
                "status": axis_status,
                "ok": axis_status == "unreachable_under_current_bounds",
                "command_results": command_results,
            }
        )
    return axis_results, aggregate_results


def _lane_closure_status(command_results: list[dict[str, Any]]) -> str:
    if not command_results:
        return "inconclusive"
    statuses = {str(result.get("status")) for result in command_results}
    if "failed" in statuses:
        return "failed"
    if "inconclusive" in statuses:
        return "inconclusive"
    return "passed"


def _obligation_closure_status(lane_results: list[dict[str, Any]], *, selected_lane_count: int, total_lane_count: int) -> str:
    if not lane_results:
        return "inconclusive"
    lane_statuses = {str(result.get("status")) for result in lane_results}
    if "failed" in lane_statuses:
        return "failed"
    if "inconclusive" in lane_statuses:
        return "inconclusive"
    if selected_lane_count != total_lane_count:
        return "partial"
    return "closed"


def run_disaster_search_expansion_plan(
    *,
    plan: str | Path | dict[str, Any] | None = None,
    axis_ids: list[str] | None = None,
    timeout_s: int = 240,
    aggregate_pytest: bool = False,
) -> dict[str, Any]:
    if plan is None:
        search_plan = build_disaster_search_expansion_plan(axis_ids=axis_ids)
    elif isinstance(plan, dict):
        search_plan = plan
    else:
        path = _resolve_path(plan)
        if path is None or not path.is_file():
            raise ValueError(f"missing disaster search expansion plan: {plan}")
        search_plan = _load_json(path)

    errors: list[str] = []
    if search_plan.get("schema") != DISASTER_SEARCH_EXPANSION_PLAN_SCHEMA:
        errors.append(f"search expansion plan schema must equal {DISASTER_SEARCH_EXPANSION_PLAN_SCHEMA}")
    if search_plan.get("ok") is not True:
        errors.append("search expansion plan is not ok")

    selected_axis_ids = set(axis_ids) if axis_ids else None
    axis_results: list[dict[str, Any]] = []
    raw_axes = search_plan.get("axes", [])
    if not isinstance(raw_axes, list):
        errors.append("axes must be a list")
        raw_axes = []

    aggregate_command_results: list[dict[str, Any]] = []
    aggregate_result = None
    if aggregate_pytest:
        aggregate_result = _run_aggregate_pytest_axes(
            raw_axes,
            selected_axis_ids=selected_axis_ids,
            timeout_s=timeout_s,
        )
    if aggregate_result is not None:
        axis_results, aggregate_command_results = aggregate_result
    else:
        for axis in raw_axes:
            if not isinstance(axis, dict):
                errors.append("axis entries must be objects")
                continue
            axis_id = str(axis.get("axis_id") or "")
            if selected_axis_ids is not None and axis_id not in selected_axis_ids:
                continue
            command_results: list[dict[str, Any]] = []
            raw_commands = axis.get("commands", [])
            if not isinstance(raw_commands, list) or not raw_commands:
                command_results.append(
                    {
                        "command": [],
                        "status": "inconclusive",
                        "ok": False,
                        "returncode": None,
                        "duration_s": 0,
                        "stdout": "",
                        "stderr": "axis has no commands",
                    }
                )
            else:
                for command in raw_commands:
                    if not isinstance(command, list) or not all(isinstance(item, str) for item in command):
                        command_results.append(
                            {
                                "command": [],
                                "status": "failed",
                                "ok": False,
                                "returncode": None,
                                "duration_s": 0,
                                "stdout": "",
                                "stderr": "axis command must be a list of strings",
                            }
                        )
                        continue
                    command_results.append(_run_obligation_command(command, timeout_s=timeout_s))
            command_statuses = {str(result.get("status")) for result in command_results}
            if "failed" in command_statuses:
                axis_status = "found_or_regressed"
            elif "inconclusive" in command_statuses:
                axis_status = "inconclusive"
            else:
                axis_status = "unreachable_under_current_bounds"
            axis_results.append(
                {
                    "axis_id": axis_id,
                    "priority_score": int(axis.get("priority_score", 0) or 0),
                    "surface_ids": axis.get("surface_ids", []),
                    "what_if": axis.get("what_if"),
                    "disaster_state_template": axis.get("disaster_state_template"),
                    "status": axis_status,
                    "ok": axis_status == "unreachable_under_current_bounds",
                    "command_results": command_results,
                }
            )

    if not axis_results:
        errors.append("no disaster search expansion axes selected")

    receipt_ok = not errors and bool(axis_results) and all(
        result.get("status") == "unreachable_under_current_bounds" for result in axis_results
    )
    return {
        "schema": DISASTER_SEARCH_EXPANSION_RECEIPT_SCHEMA,
        "ok": receipt_ok,
        "generated_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "errors": errors,
        "policy": {
            "axis_ids": None if axis_ids is None else list(axis_ids),
            "timeout_s": timeout_s,
            "skips_are_inconclusive": True,
            "claim_tier": "bounded_search_receipt",
        },
        "selected_axis_count": len(axis_results),
        "unreachable_count": sum(1 for result in axis_results if result.get("status") == "unreachable_under_current_bounds"),
        "failed_count": sum(1 for result in axis_results if result.get("status") == "found_or_regressed"),
        "inconclusive_count": sum(1 for result in axis_results if result.get("status") == "inconclusive"),
        "aggregate_command_results": aggregate_command_results,
        "axis_results": sorted(axis_results, key=lambda row: (-int(row["priority_score"]), str(row["axis_id"]))),
    }


def run_stateful_disaster_proof_obligations(
    *,
    packet: str | Path | dict[str, Any],
    surface_ids: list[str] | None = None,
    lane_kinds: list[str] | None = None,
    timeout_s: int = 180,
) -> dict[str, Any]:
    proof_packet = _load_proof_obligation_packet(packet)
    errors: list[str] = []
    warnings: list[str] = []
    if proof_packet.get("schema") != PROOF_OBLIGATION_PACKET_SCHEMA:
        errors.append(f"proof-obligation packet schema must equal {PROOF_OBLIGATION_PACKET_SCHEMA}")
    if proof_packet.get("ok") is not True:
        errors.append("proof-obligation packet is not ok")

    surface_filter = set(surface_ids) if surface_ids else None
    lane_filter = set(lane_kinds) if lane_kinds else None
    selected = _selected_obligations(proof_packet, surface_ids=surface_filter)
    if not selected:
        errors.append("no proof obligations selected")

    obligation_results: list[dict[str, Any]] = []
    for obligation in selected:
        lanes = obligation.get("lanes", [])
        if not isinstance(lanes, list):
            errors.append(f"{obligation.get('surface_id')}: lanes must be a list")
            continue
        total_lane_count = len([lane for lane in lanes if isinstance(lane, dict)])
        selected_lanes = [
            lane
            for lane in lanes
            if isinstance(lane, dict) and (lane_filter is None or str(lane.get("kind")) in lane_filter)
        ]
        if not selected_lanes:
            warnings.append(f"{obligation.get('surface_id')}: no lanes selected")
        lane_results: list[dict[str, Any]] = []
        for lane in selected_lanes:
            missing_artifacts = [str(item) for item in lane.get("missing_artifacts", []) if isinstance(item, str)]
            command_results: list[dict[str, Any]] = []
            if missing_artifacts:
                command_results.append(
                    {
                        "command": [],
                        "status": "failed",
                        "ok": False,
                        "returncode": None,
                        "duration_s": 0,
                        "stdout": "",
                        "stderr": "missing artifacts: " + ", ".join(missing_artifacts),
                    }
                )
            else:
                commands = lane.get("commands", [])
                if not isinstance(commands, list) or not commands:
                    command_results.append(
                        {
                            "command": [],
                            "status": "inconclusive",
                            "ok": False,
                            "returncode": None,
                            "duration_s": 0,
                            "stdout": "",
                            "stderr": "lane has no commands",
                        }
                    )
                else:
                    for command in commands:
                        if not isinstance(command, list) or not all(isinstance(item, str) for item in command):
                            command_results.append(
                                {
                                    "command": [],
                                    "status": "failed",
                                    "ok": False,
                                    "returncode": None,
                                    "duration_s": 0,
                                    "stdout": "",
                                    "stderr": "lane command must be a list of strings",
                                }
                            )
                            continue
                        command_results.append(_run_obligation_command(command, timeout_s=timeout_s))
            lane_status = _lane_closure_status(command_results)
            lane_results.append(
                {
                    "kind": lane.get("kind"),
                    "name": lane.get("name"),
                    "status": lane_status,
                    "ok": lane_status == "passed",
                    "command_results": command_results,
                }
            )
        closure_status = _obligation_closure_status(
            lane_results,
            selected_lane_count=len(selected_lanes),
            total_lane_count=total_lane_count,
        )
        obligation_results.append(
            {
                "obligation_id": obligation.get("obligation_id"),
                "surface_id": obligation.get("surface_id"),
                "target_evidence_class": obligation.get("target_evidence_class"),
                "closure_status": closure_status,
                "ok": closure_status == "closed",
                "selected_lane_count": len(selected_lanes),
                "total_lane_count": total_lane_count,
                "lane_results": lane_results,
            }
        )

    receipt_ok = not errors and bool(obligation_results) and all(result.get("closure_status") == "closed" for result in obligation_results)
    return {
        "schema": PROOF_OBLIGATION_CLOSURE_RECEIPT_SCHEMA,
        "ok": receipt_ok,
        "generated_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "errors": errors,
        "warnings": warnings,
        "policy": {
            "surface_ids": None if surface_ids is None else list(surface_ids),
            "lane_kinds": None if lane_kinds is None else list(lane_kinds),
            "timeout_s": timeout_s,
            "skips_are_inconclusive": True,
        },
        "selected_obligation_count": len(obligation_results),
        "closed_count": sum(1 for result in obligation_results if result.get("closure_status") == "closed"),
        "failed_count": sum(1 for result in obligation_results if result.get("closure_status") == "failed"),
        "inconclusive_count": sum(1 for result in obligation_results if result.get("closure_status") == "inconclusive"),
        "partial_count": sum(1 for result in obligation_results if result.get("closure_status") == "partial"),
        "obligation_results": obligation_results,
    }
