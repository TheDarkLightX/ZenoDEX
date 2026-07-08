#!/usr/bin/env python3
"""Local ZenoProof v0 artifact and Oracle O4 bridge verifier."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping, Sequence

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from src.integration.proof_verifier import ProofVerifierConfig, make_proof_verifier  # noqa: E402
from src.state.canonical import canonical_json_bytes  # noqa: E402
from tools.zenodex_oracle import sample_bundle, verify_bundle  # noqa: E402

ARTIFACT_SCHEMA = "zenodex.zenoproof.artifact.v0"
REGISTRY_SCHEMA = "zenodex.zenoproof.registry_manifest.v0"
VERIFY_RESULT_SCHEMA = "zenodex.zenoproof.verify_result.v0"
ORACLE_BRIDGE_SCHEMA = "zenodex.zenoproof.oracle_o4_bridge.v0"
ORACLE_BRIDGE_RESULT_SCHEMA = "zenodex.zenoproof.oracle_o4_bridge_result.v0"
O5_INDEPENDENCE_WITNESS_SCHEMA = "zenodex.zenoproof.o5_independence_witness.v0"
O5_INDEPENDENCE_WITNESS_RESULT_SCHEMA = "zenodex.zenoproof.o5_independence_witness_result.v0"
REWARD_GATE_SCHEMA = "zenodex.zenoproof.reward_gate.v0"
REWARD_GATE_RESULT_SCHEMA = "zenodex.zenoproof.reward_gate_result.v0"
MAX_JSON_BYTES = 1_000_000
MAX_EPOCH = 2**63 - 1
MAX_REWARD_AMOUNT = 10**30
MAX_VERIFIER_TIMEOUT_MS = 300_000
HASH_PREFIX = "sha256:"
HASH_HEX_LEN = 64
SUPPORTED_PROOF_KINDS = {
    "lean",
    "tla",
    "ltlf",
    "esso",
    "risc0",
    "smt",
    "morph_bundle",
    "julia_witness",
    "public_replay",
}
ARTIFACT_KEYS = {
    "schema",
    "proof_id",
    "proof_kind",
    "claim_id",
    "statement_hash",
    "assumptions_hash",
    "input_commitment_root",
    "output_commitment_root",
    "verifier_id",
    "verifier_policy_root",
    "toolchain_id",
    "issued_at_epoch",
    "expires_at_epoch",
    "result",
    "non_claims",
}
REGISTRY_KEYS = {"schema", "policy_epoch", "verifiers", "claims"}
VERIFIER_KEYS = {
    "verifier_id",
    "name",
    "proof_kinds",
    "current_policy_root",
    "toolchain_ids",
    "revoked",
    "max_input_bytes",
    "timeout_ms",
    "execution_mode",
    "verifier_command",
    "allow_path_lookup",
}
CLAIM_KEYS = {
    "claim_id",
    "statement_hash",
    "assumptions_hash",
    "dependency_claim_ids",
    "evidence_class",
    "replay_command",
    "non_claims",
}
ORACLE_BRIDGE_KEYS = {
    "schema",
    "bridge_id",
    "receipt_bundle",
    "proof_artifact",
    "o5_independence_witness",
    "target_evidence_class",
}
O5_INDEPENDENCE_WITNESS_KEYS = {
    "schema",
    "witness_id",
    "primary_proof_id",
    "primary_claim_id",
    "expected_input_commitment_root",
    "expected_output_commitment_root",
    "crosscheck_proof_artifacts",
    "required_distinct_verifier_count",
    "required_distinct_proof_kind_count",
    "non_claims",
}
REWARD_GATE_KEYS = {
    "schema",
    "proof_artifact",
    "reward_pool_before_e8",
    "reward_amount_e8",
    "reward_pool_after_e8",
    "previously_rewarded_claim_ids",
    "expected_claim_id",
    "expected_input_commitment_root",
    "expected_output_commitment_root",
}
SAMPLE_VERIFIER_ID = "sha256:6711b2653c3b787ef3aed537088e8552eaaa357ad82dfb838c1e39af3dbd70f8"
SAMPLE_POLICY_ROOT = "sha256:708f1414569312b4cc6bc398568c1fec8fe0b31ea2ab4130284334ec19f11f32"
SAMPLE_TOOLCHAIN_ID = "sha256:bad2dc4aa1a34f048eacc5831b9de8c849fe3cc2aa42cc5123c3538e8080d529"
SAMPLE_CROSSCHECK_VERIFIER_ID = (
    "sha256:" + hashlib.sha256(b"zenoproof.sample.o5.crosscheck.verifier").hexdigest()
)
SAMPLE_CROSSCHECK_POLICY_ROOT = (
    "sha256:" + hashlib.sha256(b"zenoproof.sample.o5.crosscheck.policy").hexdigest()
)
SAMPLE_CROSSCHECK_TOOLCHAIN_ID = (
    "sha256:" + hashlib.sha256(b"zenoproof.sample.o5.crosscheck.toolchain").hexdigest()
)
SAMPLE_CLAIM_ID = "sha256:33d0e19ca78b8e80698e67444a4f93d73b921ad26c463ecb7d0be761c7d53b00"
SAMPLE_STATEMENT_HASH = "sha256:ac5610756b449e45e5da26c1c0a4bcffc0083f3647ceb3c48cdc04e8abe980d2"
SAMPLE_ASSUMPTIONS_HASH = "sha256:a5764ec3b0423bebd136337f6f6e2b3319339f8a75487ac835cf8898b41349d3"
SAMPLE_O5_CLAIM_ID = "sha256:" + hashlib.sha256(b"zenoproof.sample.o5.claim").hexdigest()
SAMPLE_O5_STATEMENT_HASH = "sha256:" + hashlib.sha256(b"zenoproof.sample.o5.statement").hexdigest()
SAMPLE_O5_ASSUMPTIONS_HASH = "sha256:" + hashlib.sha256(b"zenoproof.sample.o5.assumptions").hexdigest()
PUBLIC_REPLAY_PROFILE = "zeno_oracle_workflow_evidence_status_v1"
PUBLIC_REPLAY_VERIFIER_ID = "sha256:055f67e1cc7f1a93f9b49274b7b5346e83ee7a811b8ec8b51f8b5afd553043ba"
PUBLIC_REPLAY_POLICY_ROOT = "sha256:bb07b1b0a598375eb12df303c389d997ef0bc1f015e22a474bc2ec329b72fa6c"
PUBLIC_REPLAY_TOOLCHAIN_ID = "sha256:b1fdc2948c8ba3e58bd705ee8085d28996ea3e9ba26a3b4957c88cbc65b60a29"
PUBLIC_REPLAY_CLAIM_ID = "sha256:0091a231f6fe6bbdf852cdf23b67d3e139c55afd3cad5bbed9f1e4be54095682"
PUBLIC_REPLAY_STATEMENT_HASH = "sha256:773a777d8c4c19d541a204f87322d711713e050a74025f2451b50acb95307b0f"
PUBLIC_REPLAY_ASSUMPTIONS_HASH = "sha256:42297de8bfbb206e41841e4137f83f6bc87eb0ad8f2a7b894d5ea8b18964e249"
JULIA_REPLAY_PROFILE = "zeno_oracle_math_witness_sweep_julia_v1"
JULIA_REPLAY_VERIFIER_ID = "sha256:74f91670c6d852c843add1a76b007277d8a729a07050c06baa19baea437a2b9b"
JULIA_REPLAY_POLICY_ROOT = "sha256:94a277186469997af46e1027c272a7f8c7740db0f3eba272e744e41056b7a768"
JULIA_REPLAY_TOOLCHAIN_ID = "sha256:29c47e97f280e147a0b3ee5607448e0406a4bf54da5cfcb056feef48373010ea"
JULIA_REPLAY_CLAIM_ID = "sha256:66099f8f5d2200152e88543ccaa7d982718ef10b800e6e8480561580e800e43f"
JULIA_REPLAY_STATEMENT_HASH = "sha256:d7360c57ce1a34dc35ec3d8cbfed5d24d1173aa170e4c3c1860ef972d5449f5b"
JULIA_REPLAY_ASSUMPTIONS_HASH = "sha256:5215763c57ec0176053bc1e2e3e8209818c29736f31c708783dec77e949005dc"
LEAN_REPLAY_PROFILE = "zeno_oracle_math_witness_anchor_lean_v1"
LEAN_REPLAY_VERIFIER_ID = "sha256:57263ed213841b4b1875bc25a1bb743579c5a2bfb618e2f9d2cee1d6bc5e0fa5"
LEAN_REPLAY_POLICY_ROOT = "sha256:b6d77205af54f3200ca69dcd101790abe9f6ecdb7fd35b4bcdffd72a96211a2c"
LEAN_REPLAY_TOOLCHAIN_ID = "sha256:d77c7a7c3eb2c3d4cd0f5d79004328ac21d220d50f28e7c84da191bdf2eee747"
LEAN_REPLAY_CLAIM_ID = "sha256:f30a0311aa74ae3847b8dd34c19881f46f8acfff3c32f93f6e1bac798113a05d"
LEAN_REPLAY_STATEMENT_HASH = "sha256:4171758f2adef37bb4d40a5595e8981e234fa98cdb509138ae0ce1c392e00a28"
LEAN_REPLAY_ASSUMPTIONS_HASH = "sha256:31d9d09769a722ea6314d583df67205c6526301827a9cbe0e7412baf4d9e4907"
SMT_REPLAY_PROFILE = "zeno_oracle_smt_freshness_v1"
SMT_REPLAY_VERIFIER_ID = "sha256:ecd5d2ebafe76eeb145898c42d50b7fbc68d97738bc6625113c33921c5b128f8"
SMT_REPLAY_POLICY_ROOT = "sha256:05117af3de75fea6846efdf3a7300ea0bbc588e1bfe66eaf77e6233e58130a37"
SMT_REPLAY_TOOLCHAIN_ID = "sha256:d2ea6c632aa61169a66a3e1756dc037382460867dfc848c1873e3e12e570d8af"
SMT_REPLAY_CLAIM_ID = "sha256:fa4eadc157222f5dd24122accce3616fc8c35f4667889ee601db05fa15d5bc8c"
SMT_REPLAY_STATEMENT_HASH = "sha256:49b641b6cfca0821ab414780680e9a48dea0111abb99f9f095dda16bec42b769"
SMT_REPLAY_ASSUMPTIONS_HASH = "sha256:ef1d20cc94812953ff4810adc6b517aa8dfbeeaac290344705823bb47bca0987"
PUBLIC_REPLAY_PROFILE_CONFIGS: dict[str, dict[str, Any]] = {
    PUBLIC_REPLAY_PROFILE: {
        "name": "zeno-oracle-workflow-evidence-public-replay-v0",
        "proof_kind": "public_replay",
        "verifier_id": PUBLIC_REPLAY_VERIFIER_ID,
        "policy_root": PUBLIC_REPLAY_POLICY_ROOT,
        "toolchain_id": PUBLIC_REPLAY_TOOLCHAIN_ID,
        "claim_id": PUBLIC_REPLAY_CLAIM_ID,
        "statement_hash": PUBLIC_REPLAY_STATEMENT_HASH,
        "assumptions_hash": PUBLIC_REPLAY_ASSUMPTIONS_HASH,
        "timeout_ms": 15_000,
        "replay_command": "python3 tools/zeno_oracle_workflow_evidence_status.py --format json",
        "expected_schema": "zenodex.oracle.workflow_evidence_status.v1",
        "non_claims": [
            "does_not_claim_private_popperpad_publication",
            "does_not_claim_external_morph_execution",
            "does_not_claim_external_tla_ltlf_esso_execution",
            "does_not_claim_production_oracle_truth",
        ],
    },
    JULIA_REPLAY_PROFILE: {
        "name": "zeno-oracle-julia-math-witness-public-replay-v0",
        "proof_kind": "julia_witness",
        "verifier_id": JULIA_REPLAY_VERIFIER_ID,
        "policy_root": JULIA_REPLAY_POLICY_ROOT,
        "toolchain_id": JULIA_REPLAY_TOOLCHAIN_ID,
        "claim_id": JULIA_REPLAY_CLAIM_ID,
        "statement_hash": JULIA_REPLAY_STATEMENT_HASH,
        "assumptions_hash": JULIA_REPLAY_ASSUMPTIONS_HASH,
        "timeout_ms": 20_000,
        "replay_command": "julia tools/zeno_oracle_math_witness_sweep.jl --json",
        "expected_schema": "zenodex.oracle.math_witness_sweep.v1",
        "non_claims": [
            "does_not_claim_generalized_median_theorems",
            "does_not_claim_production_oracle_benefit_laws",
        ],
    },
    LEAN_REPLAY_PROFILE: {
        "name": "zeno-oracle-lean-math-anchor-public-replay-v0",
        "proof_kind": "lean",
        "verifier_id": LEAN_REPLAY_VERIFIER_ID,
        "policy_root": LEAN_REPLAY_POLICY_ROOT,
        "toolchain_id": LEAN_REPLAY_TOOLCHAIN_ID,
        "claim_id": LEAN_REPLAY_CLAIM_ID,
        "statement_hash": LEAN_REPLAY_STATEMENT_HASH,
        "assumptions_hash": LEAN_REPLAY_ASSUMPTIONS_HASH,
        "timeout_ms": 30_000,
        "replay_command": "lean lean-mathlib/Proofs/ZenoOracleMathWitness.lean",
        "expected_schema": "zenodex.oracle.lean_math_witness_anchor_replay.v1",
        "non_claims": [
            "does_not_claim_generalized_median_theorems",
            "does_not_claim_full_sync_gate_composition",
        ],
    },
    SMT_REPLAY_PROFILE: {
        "name": "zeno-oracle-smt-freshness-public-replay-v0",
        "proof_kind": "smt",
        "verifier_id": SMT_REPLAY_VERIFIER_ID,
        "policy_root": SMT_REPLAY_POLICY_ROOT,
        "toolchain_id": SMT_REPLAY_TOOLCHAIN_ID,
        "claim_id": SMT_REPLAY_CLAIM_ID,
        "statement_hash": SMT_REPLAY_STATEMENT_HASH,
        "assumptions_hash": SMT_REPLAY_ASSUMPTIONS_HASH,
        "timeout_ms": 20_000,
        "replay_command": "python3 tools/zeno_oracle_smt_freshness_replay.py --format json",
        "expected_schema": "zenodex.oracle.smt_freshness_replay.v1",
        "non_claims": [
            "does_not_claim_tau_binary_equivalence",
            "does_not_claim_unbounded_temporal_liveness",
            "does_not_claim_production_oracle_truth",
        ],
    },
}


@dataclass(frozen=True)
class ZenoProofVerifyResult:
    status: str
    errors: list[str]
    proof_ok: bool
    binding_ok: bool
    policy_ok: bool
    freshness_ok: bool
    claim_id: str | None = None
    proof_id: str | None = None
    verifier_id: str | None = None
    evidence_class: str | None = None

    def to_json_obj(self) -> dict[str, Any]:
        return {
            "schema": VERIFY_RESULT_SCHEMA,
            "ok": self.status == "accepted",
            "status": self.status,
            "proof_ok": self.proof_ok,
            "binding_ok": self.binding_ok,
            "policy_ok": self.policy_ok,
            "freshness_ok": self.freshness_ok,
            "claim_id": self.claim_id,
            "proof_id": self.proof_id,
            "verifier_id": self.verifier_id,
            "evidence_class": self.evidence_class,
            "errors": list(self.errors),
        }


@dataclass(frozen=True)
class OracleO4BridgeResult:
    status: str
    errors: list[str]
    receipt_status: str | None = None
    proof_status: str | None = None
    o5_witness_status: str | None = None
    query_id: str | None = None
    value_hash: str | None = None
    consumer_module: str | None = None
    action_kind: str | None = None
    action_id: str | None = None
    proof_id: str | None = None
    claim_id: str | None = None
    target_evidence_class: str | None = None

    def to_json_obj(self) -> dict[str, Any]:
        return {
            "schema": ORACLE_BRIDGE_RESULT_SCHEMA,
            "ok": self.status == "accepted",
            "status": self.status,
            "receipt_status": self.receipt_status,
            "proof_status": self.proof_status,
            "o5_witness_status": self.o5_witness_status,
            "query_id": self.query_id,
            "value_hash": self.value_hash,
            "consumer_module": self.consumer_module,
            "action_kind": self.action_kind,
            "action_id": self.action_id,
            "proof_id": self.proof_id,
            "claim_id": self.claim_id,
            "target_evidence_class": self.target_evidence_class,
            "errors": list(self.errors),
            "not_claimed": [
                "does_not_claim_production_oracle_truth",
                "does_not_claim_live_proof_network",
            ],
        }


@dataclass(frozen=True)
class O5IndependenceWitnessResult:
    status: str
    errors: list[str]
    primary_claim_id: str | None = None
    primary_proof_id: str | None = None
    crosscheck_count: int = 0
    distinct_verifier_count: int = 0
    distinct_proof_kind_count: int = 0
    claim_ids: list[str] | None = None

    def to_json_obj(self) -> dict[str, Any]:
        return {
            "schema": O5_INDEPENDENCE_WITNESS_RESULT_SCHEMA,
            "ok": self.status == "accepted",
            "status": self.status,
            "primary_claim_id": self.primary_claim_id,
            "primary_proof_id": self.primary_proof_id,
            "crosscheck_count": self.crosscheck_count,
            "distinct_verifier_count": self.distinct_verifier_count,
            "distinct_proof_kind_count": self.distinct_proof_kind_count,
            "claim_ids": list(self.claim_ids or []),
            "errors": list(self.errors),
            "not_claimed": [
                "does_not_claim_live_proof_network",
                "does_not_claim_independence_beyond_declared_verifier_and_proof_kind_separation",
            ],
        }


@dataclass(frozen=True)
class ZenoProofRewardGateResult:
    status: str
    errors: list[str]
    checks: Mapping[str, bool]
    claim_id: str | None = None
    proof_id: str | None = None
    reward_amount_e8: int | None = None
    reward_pool_before_e8: int | None = None
    reward_pool_after_e8: int | None = None

    def to_json_obj(self) -> dict[str, Any]:
        return {
            "schema": REWARD_GATE_RESULT_SCHEMA,
            "ok": self.status == "accepted",
            "status": self.status,
            "claim_id": self.claim_id,
            "proof_id": self.proof_id,
            "reward_amount_e8": self.reward_amount_e8,
            "reward_pool_before_e8": self.reward_pool_before_e8,
            "reward_pool_after_e8": self.reward_pool_after_e8,
            "checks": dict(self.checks),
            "errors": list(self.errors),
            "not_claimed": [
                "does_not_claim_live_proof_mining_payouts",
                "does_not_claim_token_settlement",
                "does_not_claim_live_proof_network",
            ],
        }


def sha256_json(obj: Any) -> str:
    return HASH_PREFIX + hashlib.sha256(canonical_json_bytes(obj)).hexdigest()


def sample_hash(tag: str) -> str:
    return HASH_PREFIX + hashlib.sha256(tag.encode("utf-8")).hexdigest()


def artifact_content_hash(artifact: Mapping[str, Any]) -> str:
    return sha256_json({key: value for key, value in artifact.items() if key != "proof_id"})


def o5_independence_witness_content_hash(witness: Mapping[str, Any]) -> str:
    return sha256_json({key: value for key, value in witness.items() if key != "witness_id"})


def oracle_o4_input_root(bundle: Mapping[str, Any]) -> str:
    result = verify_bundle(bundle)
    if result.status != "accepted":
        raise ValueError("receipt bundle must be accepted before deriving Oracle O4 input root")
    payload = {
        "schema": "zenodex.zenoproof.oracle_o4_input.v0",
        "query_id": result.query_id,
        "value_hash": result.value_hash,
        "read_receipt_id": result.read_receipt_id,
        "consumer_action_receipt_id": result.consumer_action_receipt_id,
        "consumer_module": result.consumer_module,
        "action_kind": result.action_kind,
        "action_id": result.action_id,
        "observed_epoch": result.observed_epoch,
        "expires_at_epoch": result.expires_at_epoch,
        "action_epoch": result.action_epoch,
    }
    return sha256_json(payload)


def _public_replay_verifier_manifest(profile: str) -> dict[str, Any]:
    cfg = PUBLIC_REPLAY_PROFILE_CONFIGS[profile]
    return {
        "verifier_id": cfg["verifier_id"],
        "name": cfg["name"],
        "proof_kinds": [cfg["proof_kind"]],
        "current_policy_root": cfg["policy_root"],
        "toolchain_ids": [cfg["toolchain_id"]],
        "revoked": False,
        "max_input_bytes": MAX_JSON_BYTES,
        "timeout_ms": cfg["timeout_ms"],
        "execution_mode": "subprocess_json",
        "verifier_command": [
            "python3",
            "tools/zenoproof_public_replay_verifier.py",
            "--profile",
            profile,
        ],
        "allow_path_lookup": True,
    }


def _public_replay_claim_manifest(profile: str) -> dict[str, Any]:
    cfg = PUBLIC_REPLAY_PROFILE_CONFIGS[profile]
    return {
        "claim_id": cfg["claim_id"],
        "statement_hash": cfg["statement_hash"],
        "assumptions_hash": cfg["assumptions_hash"],
        "dependency_claim_ids": [SAMPLE_CLAIM_ID],
        "evidence_class": "O4",
        "replay_command": cfg["replay_command"],
        "non_claims": list(cfg["non_claims"]),
    }


def sample_registry() -> dict[str, Any]:
    return {
        "schema": REGISTRY_SCHEMA,
        "policy_epoch": 1,
        "verifiers": [
            {
                "verifier_id": SAMPLE_VERIFIER_ID,
                "name": "local-static-accept-v0",
                "proof_kinds": ["lean", "tla", "ltlf", "esso", "risc0", "smt", "morph_bundle", "julia_witness"],
                "current_policy_root": SAMPLE_POLICY_ROOT,
                "toolchain_ids": [SAMPLE_TOOLCHAIN_ID],
                "revoked": False,
                "max_input_bytes": MAX_JSON_BYTES,
                "timeout_ms": 1000,
                "execution_mode": "local_static_accept",
                "verifier_command": [],
                "allow_path_lookup": False,
            },
            {
                "verifier_id": SAMPLE_CROSSCHECK_VERIFIER_ID,
                "name": "local-static-crosscheck-v0",
                "proof_kinds": ["lean", "smt"],
                "current_policy_root": SAMPLE_CROSSCHECK_POLICY_ROOT,
                "toolchain_ids": [SAMPLE_CROSSCHECK_TOOLCHAIN_ID],
                "revoked": False,
                "max_input_bytes": MAX_JSON_BYTES,
                "timeout_ms": 1000,
                "execution_mode": "local_static_accept",
                "verifier_command": [],
                "allow_path_lookup": False,
            },
            _public_replay_verifier_manifest(PUBLIC_REPLAY_PROFILE),
            _public_replay_verifier_manifest(JULIA_REPLAY_PROFILE),
            _public_replay_verifier_manifest(LEAN_REPLAY_PROFILE),
            _public_replay_verifier_manifest(SMT_REPLAY_PROFILE),
        ],
        "claims": [
            {
                "claim_id": SAMPLE_CLAIM_ID,
                "statement_hash": SAMPLE_STATEMENT_HASH,
                "assumptions_hash": SAMPLE_ASSUMPTIONS_HASH,
                "dependency_claim_ids": [],
                "evidence_class": "O4",
                "replay_command": "python3 tools/zenoproof_verify.py self-test --registry tools/zenoproof_registry_manifest.json",
                "non_claims": ["does_not_claim_live_proof_network"],
            },
            {
                "claim_id": SAMPLE_O5_CLAIM_ID,
                "statement_hash": SAMPLE_O5_STATEMENT_HASH,
                "assumptions_hash": SAMPLE_O5_ASSUMPTIONS_HASH,
                "dependency_claim_ids": [SAMPLE_CLAIM_ID],
                "evidence_class": "O5",
                "replay_command": "python3 tools/zenoproof_verify.py self-test --registry tools/zenoproof_registry_manifest.json",
                "non_claims": [
                    "does_not_claim_live_proof_network",
                    "does_not_claim_independence_beyond_declared_verifier_and_proof_kind_separation",
                ],
            },
            _public_replay_claim_manifest(PUBLIC_REPLAY_PROFILE),
            _public_replay_claim_manifest(JULIA_REPLAY_PROFILE),
            _public_replay_claim_manifest(LEAN_REPLAY_PROFILE),
            _public_replay_claim_manifest(SMT_REPLAY_PROFILE),
        ],
    }


def sample_artifact(
    *,
    input_commitment_root: str | None = None,
    output_commitment_root: str | None = None,
) -> dict[str, Any]:
    artifact = {
        "schema": ARTIFACT_SCHEMA,
        "proof_kind": "tla",
        "claim_id": SAMPLE_CLAIM_ID,
        "statement_hash": SAMPLE_STATEMENT_HASH,
        "assumptions_hash": SAMPLE_ASSUMPTIONS_HASH,
        "input_commitment_root": input_commitment_root or sample_hash("zenoproof.input.sample"),
        "output_commitment_root": output_commitment_root or sample_hash("zenoproof.output.sample"),
        "verifier_id": SAMPLE_VERIFIER_ID,
        "verifier_policy_root": SAMPLE_POLICY_ROOT,
        "toolchain_id": SAMPLE_TOOLCHAIN_ID,
        "issued_at_epoch": 100,
        "expires_at_epoch": 200,
        "result": "accepted",
        "non_claims": ["does_not_claim_live_proof_network"],
    }
    artifact["proof_id"] = artifact_content_hash(artifact)
    return artifact


def sample_o5_artifact(
    *,
    input_commitment_root: str | None = None,
    output_commitment_root: str | None = None,
) -> dict[str, Any]:
    artifact = {
        "schema": ARTIFACT_SCHEMA,
        "proof_kind": "smt",
        "claim_id": SAMPLE_O5_CLAIM_ID,
        "statement_hash": SAMPLE_O5_STATEMENT_HASH,
        "assumptions_hash": SAMPLE_O5_ASSUMPTIONS_HASH,
        "input_commitment_root": input_commitment_root or sample_hash("zenoproof.o5.input.sample"),
        "output_commitment_root": output_commitment_root or sample_hash("zenoproof.o5.output.sample"),
        "verifier_id": SAMPLE_VERIFIER_ID,
        "verifier_policy_root": SAMPLE_POLICY_ROOT,
        "toolchain_id": SAMPLE_TOOLCHAIN_ID,
        "issued_at_epoch": 100,
        "expires_at_epoch": 200,
        "result": "accepted",
        "non_claims": [
            "does_not_claim_live_proof_network",
            "does_not_claim_independence_beyond_declared_verifier_and_proof_kind_separation",
        ],
    }
    artifact["proof_id"] = artifact_content_hash(artifact)
    return artifact


def sample_o5_crosscheck_artifact(
    *,
    input_commitment_root: str,
    output_commitment_root: str,
) -> dict[str, Any]:
    artifact = {
        "schema": ARTIFACT_SCHEMA,
        "proof_kind": "lean",
        "claim_id": SAMPLE_CLAIM_ID,
        "statement_hash": SAMPLE_STATEMENT_HASH,
        "assumptions_hash": SAMPLE_ASSUMPTIONS_HASH,
        "input_commitment_root": input_commitment_root,
        "output_commitment_root": output_commitment_root,
        "verifier_id": SAMPLE_CROSSCHECK_VERIFIER_ID,
        "verifier_policy_root": SAMPLE_CROSSCHECK_POLICY_ROOT,
        "toolchain_id": SAMPLE_CROSSCHECK_TOOLCHAIN_ID,
        "issued_at_epoch": 100,
        "expires_at_epoch": 200,
        "result": "accepted",
        "non_claims": ["does_not_claim_live_proof_network"],
    }
    artifact["proof_id"] = artifact_content_hash(artifact)
    return artifact


def sample_o5_independence_witness(primary_artifact: Mapping[str, Any]) -> dict[str, Any]:
    input_root = str(primary_artifact["input_commitment_root"])
    output_root = str(primary_artifact["output_commitment_root"])
    witness = {
        "schema": O5_INDEPENDENCE_WITNESS_SCHEMA,
        "primary_proof_id": primary_artifact["proof_id"],
        "primary_claim_id": primary_artifact["claim_id"],
        "expected_input_commitment_root": input_root,
        "expected_output_commitment_root": output_root,
        "crosscheck_proof_artifacts": [
            sample_o5_crosscheck_artifact(
                input_commitment_root=input_root,
                output_commitment_root=output_root,
            )
        ],
        "required_distinct_verifier_count": 2,
        "required_distinct_proof_kind_count": 2,
        "non_claims": [
            "does_not_claim_live_proof_network",
            "does_not_claim_independence_beyond_declared_verifier_and_proof_kind_separation",
        ],
    }
    witness["witness_id"] = o5_independence_witness_content_hash(witness)
    return witness


def public_replay_input_root(profile: str = PUBLIC_REPLAY_PROFILE) -> str:
    cfg = PUBLIC_REPLAY_PROFILE_CONFIGS.get(profile)
    if cfg is None:
        raise ValueError(f"unknown_public_replay_profile:{profile}")
    return sha256_json(
        {
            "schema": "zenodex.zenoproof.public_replay_input.v0",
            "profile": profile,
            "replay_command": cfg["replay_command"],
            "expected_schema": cfg["expected_schema"],
            "expected_status": "accepted",
        }
    )


def public_replay_output_root(profile: str = PUBLIC_REPLAY_PROFILE) -> str:
    if profile not in PUBLIC_REPLAY_PROFILE_CONFIGS:
        raise ValueError(f"unknown_public_replay_profile:{profile}")

    return sha256_json(run_public_replay_profile(profile))


def run_public_replay_profile(profile: str) -> Mapping[str, Any]:
    cfg = PUBLIC_REPLAY_PROFILE_CONFIGS.get(profile)
    if cfg is None:
        raise ValueError(f"unknown_public_replay_profile:{profile}")
    timeout_s = float(int(cfg["timeout_ms"])) / 1000.0

    if profile == PUBLIC_REPLAY_PROFILE:
        proc = subprocess.run(
            [sys.executable, "tools/zeno_oracle_workflow_evidence_status.py", "--format", "json"],
            cwd=ROOT,
            check=False,
            capture_output=True,
            text=True,
            timeout=timeout_s,
        )
        receipt = _load_json_stdout(proc.stdout, "workflow_status")
        if proc.returncode != 0:
            raise ValueError(f"workflow_status_failed:{proc.returncode}")
        _require_replay_receipt(receipt, expected_schema=str(cfg["expected_schema"]))
        if receipt.get("accepted_lane_count") != receipt.get("lane_count"):
            raise ValueError("workflow_status_lane_count_mismatch")
        if receipt.get("failed_lane_count") != 0:
            raise ValueError("workflow_status_failed_lanes")
        return receipt

    if profile == JULIA_REPLAY_PROFILE:
        proc = subprocess.run(
            ["julia", "tools/zeno_oracle_math_witness_sweep.jl", "--json"],
            cwd=ROOT,
            check=False,
            capture_output=True,
            text=True,
            timeout=timeout_s,
        )
        receipt = _load_json_stdout(proc.stdout, "julia_math_witness")
        if proc.returncode != 0:
            raise ValueError(f"julia_math_witness_failed:{proc.returncode}")
        _require_replay_receipt(receipt, expected_schema=str(cfg["expected_schema"]))
        if receipt.get("case_count") != 10 or receipt.get("failed_count") != 0:
            raise ValueError("julia_math_witness_case_count_mismatch")
        return receipt

    if profile == LEAN_REPLAY_PROFILE:
        proc = subprocess.run(
            ["lean", "lean-mathlib/Proofs/ZenoOracleMathWitness.lean"],
            cwd=ROOT,
            check=False,
            capture_output=True,
            text=True,
            timeout=timeout_s,
        )
        lean_file = ROOT / "lean-mathlib" / "Proofs" / "ZenoOracleMathWitness.lean"
        root_file = ROOT / "lean-mathlib" / "Proofs.lean"
        placeholder_hits = _lean_placeholder_hits([lean_file, root_file])
        ok = proc.returncode == 0 and not placeholder_hits
        receipt = {
            "schema": cfg["expected_schema"],
            "ok": ok,
            "status": "accepted" if ok else "rejected",
            "file": "lean-mathlib/Proofs/ZenoOracleMathWitness.lean",
            "root_import_file": "lean-mathlib/Proofs.lean",
            "placeholder_hits": placeholder_hits,
        }
        if proc.returncode != 0:
            raise ValueError(f"lean_math_witness_failed:{proc.returncode}")
        if placeholder_hits:
            raise ValueError("lean_math_witness_placeholder_hits")
        return receipt

    if profile == SMT_REPLAY_PROFILE:
        from tools.zeno_oracle_smt_freshness_replay import build_status

        receipt = build_status()
        _require_replay_receipt(receipt, expected_schema=str(cfg["expected_schema"]))
        if receipt.get("case_count") != 6 or receipt.get("failed_count") != 0:
            raise ValueError("smt_freshness_case_count_mismatch")
        for case in receipt.get("cases", []):
            if not isinstance(case, Mapping) or case.get("ok") is not True:
                raise ValueError("smt_freshness_case_rejected")
            solvers = case.get("solvers")
            if not isinstance(solvers, list) or [row.get("solver") for row in solvers if isinstance(row, Mapping)] != ["z3", "cvc5"]:
                raise ValueError("smt_freshness_solver_set_mismatch")
            if [row.get("status") for row in solvers if isinstance(row, Mapping)] != ["unsat", "unsat"]:
                raise ValueError("smt_freshness_solver_status_mismatch")
        return receipt

    raise ValueError(f"unknown_public_replay_profile:{profile}")


def _load_json_stdout(stdout: str, label: str) -> Mapping[str, Any]:
    try:
        receipt = json.loads(stdout)
    except Exception as exc:
        raise ValueError(f"{label}_json_invalid:{exc}") from exc
    if not isinstance(receipt, Mapping):
        raise ValueError(f"{label}_receipt_must_be_object")
    return receipt


def _require_replay_receipt(receipt: Mapping[str, Any], *, expected_schema: str) -> None:
    if receipt.get("schema") != expected_schema:
        raise ValueError("public_replay_schema_mismatch")
    if receipt.get("ok") is not True or receipt.get("status") != "accepted":
        raise ValueError("public_replay_not_accepted")


def _lean_placeholder_hits(paths: Sequence[Path]) -> list[str]:
    pattern = re.compile(r"\b(sorry|admit|axiom)\b")
    hits: list[str] = []
    for path in paths:
        text = path.read_text(encoding="utf-8")
        for line_no, line in enumerate(text.splitlines(), start=1):
            if pattern.search(line):
                hits.append(f"{path.relative_to(ROOT)}:{line_no}")
    return hits


def sample_public_replay_artifact(profile: str = PUBLIC_REPLAY_PROFILE) -> dict[str, Any]:
    cfg = PUBLIC_REPLAY_PROFILE_CONFIGS[profile]
    artifact = {
        "schema": ARTIFACT_SCHEMA,
        "proof_kind": cfg["proof_kind"],
        "claim_id": cfg["claim_id"],
        "statement_hash": cfg["statement_hash"],
        "assumptions_hash": cfg["assumptions_hash"],
        "input_commitment_root": public_replay_input_root(profile),
        "output_commitment_root": public_replay_output_root(profile),
        "verifier_id": cfg["verifier_id"],
        "verifier_policy_root": cfg["policy_root"],
        "toolchain_id": cfg["toolchain_id"],
        "issued_at_epoch": 100,
        "expires_at_epoch": 200,
        "result": "accepted",
        "non_claims": list(cfg["non_claims"]),
    }
    artifact["proof_id"] = artifact_content_hash(artifact)
    return artifact


def sample_oracle_o4_bridge() -> dict[str, Any]:
    bundle = sample_bundle()
    artifact = sample_artifact(input_commitment_root=oracle_o4_input_root(bundle))
    bridge = {
        "schema": ORACLE_BRIDGE_SCHEMA,
        "receipt_bundle": bundle,
        "proof_artifact": artifact,
        "target_evidence_class": "O4",
    }
    bridge["bridge_id"] = oracle_o4_bridge_content_hash(bridge)
    return bridge


def sample_oracle_o5_bridge() -> dict[str, Any]:
    bundle = sample_bundle()
    input_root = oracle_o4_input_root(bundle)
    output_root = sample_hash("zenoproof.o5.oracle.output.sample")
    artifact = sample_o5_artifact(
        input_commitment_root=input_root,
        output_commitment_root=output_root,
    )
    bridge = {
        "schema": ORACLE_BRIDGE_SCHEMA,
        "receipt_bundle": bundle,
        "proof_artifact": artifact,
        "o5_independence_witness": sample_o5_independence_witness(artifact),
        "target_evidence_class": "O5",
    }
    bridge["bridge_id"] = oracle_o4_bridge_content_hash(bridge)
    return bridge


def sample_reward_gate() -> dict[str, Any]:
    artifact = sample_artifact()
    return {
        "schema": REWARD_GATE_SCHEMA,
        "proof_artifact": artifact,
        "reward_pool_before_e8": 100_000_000,
        "reward_amount_e8": 25_000_000,
        "reward_pool_after_e8": 75_000_000,
        "previously_rewarded_claim_ids": [],
        "expected_claim_id": artifact["claim_id"],
        "expected_input_commitment_root": artifact["input_commitment_root"],
        "expected_output_commitment_root": artifact["output_commitment_root"],
    }


def _is_hash(value: object) -> bool:
    if not isinstance(value, str):
        return False
    if not value.startswith(HASH_PREFIX):
        return False
    suffix = value[len(HASH_PREFIX) :]
    return len(suffix) == HASH_HEX_LEN and all(ch in "0123456789abcdef" for ch in suffix)


def _require_hash(obj: Mapping[str, Any], key: str, errors: list[str]) -> str | None:
    value = obj.get(key)
    if not _is_hash(value):
        errors.append(f"{key}_must_be_sha256")
        return None
    return str(value)


def _require_int_epoch(obj: Mapping[str, Any], key: str, errors: list[str]) -> int | None:
    value = obj.get(key)
    if not isinstance(value, int) or isinstance(value, bool) or value < 0 or value > MAX_EPOCH:
        errors.append(f"{key}_must_be_int_between_0_and_{MAX_EPOCH}")
        return None
    return int(value)


def _require_positive_int_at_most(
    obj: Mapping[str, Any],
    key: str,
    errors: list[str],
    *,
    label: str,
    identifier: str,
    max_value: int,
) -> int | None:
    value = obj.get(key)
    if not isinstance(value, int) or isinstance(value, bool):
        errors.append(f"{label}_must_be_positive_int:{identifier}")
        return None
    out = int(value)
    if out <= 0:
        errors.append(f"{label}_must_be_positive:{identifier}")
        return None
    if out > max_value:
        errors.append(f"{label}_too_large:{identifier}")
        return None
    return out


def _require_reward_amount(obj: Mapping[str, Any], key: str, errors: list[str]) -> int | None:
    value = obj.get(key)
    if not isinstance(value, int) or isinstance(value, bool) or value < 0 or value > MAX_REWARD_AMOUNT:
        errors.append(f"{key}_must_be_int_between_0_and_{MAX_REWARD_AMOUNT}")
        return None
    return int(value)


def _unknown_fields(
    obj: Mapping[str, Any],
    *,
    allowed: set[str],
    label: str,
    errors: list[str],
) -> None:
    for key in obj.keys():
        if not isinstance(key, str):
            errors.append(f"{label}_field_must_be_string")
        elif key not in allowed:
            errors.append(f"unknown_{label}_field:{key}")


def _str_list(value: object, *, label: str, errors: list[str]) -> list[str]:
    if not isinstance(value, list):
        errors.append(f"{label}_must_be_list")
        return []
    result: list[str] = []
    for index, item in enumerate(value):
        if not isinstance(item, str) or not item:
            errors.append(f"{label}_{index}_must_be_nonempty_string")
            continue
        result.append(str(item))
    return result


def _require_distinct(values: Sequence[str], *, label: str, identifier: str, errors: list[str]) -> None:
    if len(set(values)) != len(values):
        errors.append(f"{label}_must_be_distinct:{identifier}")


def _check_verifier_command_policy(
    verifier: Mapping[str, Any],
    *,
    verifier_id: str,
    errors: list[str],
) -> None:
    mode = verifier.get("execution_mode")
    command = verifier.get("verifier_command")
    if not isinstance(command, list):
        errors.append(f"verifier_command_must_be_list:{verifier_id}")
        command_values: list[str] = []
    else:
        command_values = []
        for index, item in enumerate(command):
            if not isinstance(item, str) or not item:
                errors.append(f"verifier_command_{index}_must_be_nonempty_string:{verifier_id}")
            else:
                command_values.append(str(item))

    allow_path_lookup = verifier.get("allow_path_lookup")
    if not isinstance(allow_path_lookup, bool):
        errors.append(f"verifier_allow_path_lookup_must_be_bool:{verifier_id}")

    if mode == "local_static_accept":
        if isinstance(command, list) and command:
            errors.append(f"verifier_local_static_command_must_be_empty:{verifier_id}")
        if allow_path_lookup is True:
            errors.append(f"verifier_local_static_allow_path_lookup_must_be_false:{verifier_id}")
    elif mode == "subprocess_json":
        if isinstance(command, list) and not command:
            errors.append(f"verifier_subprocess_command_must_be_nonempty:{verifier_id}")
        if allow_path_lookup is False and command_values and not os.path.isabs(command_values[0]):
            errors.append(f"verifier_command_must_be_absolute_when_path_lookup_disabled:{verifier_id}")
    else:
        errors.append(f"verifier_execution_mode_invalid:{verifier_id}")


def _registry_indexes(
    registry: Mapping[str, Any],
) -> tuple[dict[str, Mapping[str, Any]], dict[str, Mapping[str, Any]], list[str]]:
    errors: list[str] = []
    _unknown_fields(registry, allowed=REGISTRY_KEYS, label="registry", errors=errors)
    if registry.get("schema") != REGISTRY_SCHEMA:
        errors.append("registry_schema_mismatch")
    _require_int_epoch(registry, "policy_epoch", errors)

    verifier_index: dict[str, Mapping[str, Any]] = {}
    verifiers = registry.get("verifiers")
    if not isinstance(verifiers, list):
        errors.append("verifiers_must_be_list")
    else:
        for pos, verifier in enumerate(verifiers):
            if not isinstance(verifier, Mapping):
                errors.append(f"verifier_{pos}_must_be_object")
                continue
            _unknown_fields(verifier, allowed=VERIFIER_KEYS, label="verifier", errors=errors)
            verifier_id = _require_hash(verifier, "verifier_id", errors)
            _require_hash(verifier, "current_policy_root", errors)
            if verifier_id is None:
                continue
            if verifier_id in verifier_index:
                errors.append(f"duplicate_verifier_id:{verifier_id}")
            verifier_index[verifier_id] = verifier
            if not isinstance(verifier.get("name"), str) or not verifier.get("name"):
                errors.append(f"verifier_name_must_be_nonempty_string:{verifier_id}")
            proof_kinds = _str_list(verifier.get("proof_kinds"), label="verifier_proof_kinds", errors=errors)
            if not proof_kinds:
                errors.append(f"verifier_proof_kinds_must_be_nonempty:{verifier_id}")
            for proof_kind in proof_kinds:
                if proof_kind not in SUPPORTED_PROOF_KINDS:
                    errors.append(f"verifier_proof_kind_unsupported:{verifier_id}:{proof_kind}")
            _require_distinct(proof_kinds, label="verifier_proof_kinds", identifier=verifier_id, errors=errors)
            toolchain_ids = _str_list(verifier.get("toolchain_ids"), label="verifier_toolchain_ids", errors=errors)
            if not toolchain_ids:
                errors.append(f"verifier_toolchain_ids_must_be_nonempty:{verifier_id}")
            for toolchain_id in toolchain_ids:
                if not _is_hash(toolchain_id):
                    errors.append(f"verifier_toolchain_id_must_be_sha256:{verifier_id}:{toolchain_id}")
            _require_distinct(toolchain_ids, label="verifier_toolchain_ids", identifier=verifier_id, errors=errors)
            if not isinstance(verifier.get("revoked"), bool):
                errors.append(f"verifier_revoked_must_be_bool:{verifier_id}")
            _require_positive_int_at_most(
                verifier,
                "timeout_ms",
                errors,
                label="verifier_timeout_ms",
                identifier=verifier_id,
                max_value=MAX_VERIFIER_TIMEOUT_MS,
            )
            _require_positive_int_at_most(
                verifier,
                "max_input_bytes",
                errors,
                label="verifier_max_input_bytes",
                identifier=verifier_id,
                max_value=MAX_JSON_BYTES,
            )
            _check_verifier_command_policy(verifier, verifier_id=verifier_id, errors=errors)

    claim_index: dict[str, Mapping[str, Any]] = {}
    claims = registry.get("claims")
    if not isinstance(claims, list):
        errors.append("claims_must_be_list")
    else:
        for pos, claim in enumerate(claims):
            if not isinstance(claim, Mapping):
                errors.append(f"claim_{pos}_must_be_object")
                continue
            _unknown_fields(claim, allowed=CLAIM_KEYS, label="claim", errors=errors)
            claim_id = _require_hash(claim, "claim_id", errors)
            _require_hash(claim, "statement_hash", errors)
            _require_hash(claim, "assumptions_hash", errors)
            deps = _str_list(claim.get("dependency_claim_ids"), label="claim_dependency_claim_ids", errors=errors)
            for dep in deps:
                if not _is_hash(dep):
                    errors.append(f"claim_dependency_claim_id_must_be_sha256:{dep}")
            if claim.get("evidence_class") not in {"O4", "O5"}:
                errors.append(f"claim_evidence_class_invalid:{claim_id}")
            if not isinstance(claim.get("replay_command"), str) or not claim.get("replay_command"):
                errors.append(f"claim_replay_command_must_be_nonempty_string:{claim_id}")
            _str_list(claim.get("non_claims"), label="claim_non_claims", errors=errors)
            if claim_id is None:
                continue
            if claim_id in claim_index:
                errors.append(f"duplicate_claim_id:{claim_id}")
            claim_index[claim_id] = claim

    errors.extend(_claim_dag_errors(claim_index))
    return verifier_index, claim_index, errors


def verify_registry_manifest(registry: Mapping[str, Any]) -> list[str]:
    """Return structural registry errors, or an empty list when the manifest is valid."""
    _, _, errors = _registry_indexes(registry)
    return errors


def _claim_dag_errors(claim_index: Mapping[str, Mapping[str, Any]]) -> list[str]:
    errors: list[str] = []
    for claim_id, claim in claim_index.items():
        deps = claim.get("dependency_claim_ids")
        if not isinstance(deps, list):
            continue
        for dep in deps:
            if isinstance(dep, str) and dep not in claim_index:
                errors.append(f"claim_dependency_missing:{claim_id}->{dep}")

    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(claim_id: str) -> None:
        if claim_id in visited:
            return
        if claim_id in visiting:
            errors.append(f"claim_dependency_cycle:{claim_id}")
            return
        visiting.add(claim_id)
        deps = claim_index[claim_id].get("dependency_claim_ids")
        if isinstance(deps, list):
            for dep in deps:
                if isinstance(dep, str) and dep in claim_index:
                    visit(dep)
        visiting.remove(claim_id)
        visited.add(claim_id)

    for claim_id in claim_index:
        visit(claim_id)
    return errors


def verify_zenoproof_artifact(
    artifact: Mapping[str, Any],
    registry: Mapping[str, Any],
    *,
    now_epoch: int,
    expected_claim_id: str | None = None,
    expected_input_commitment_root: str | None = None,
    expected_output_commitment_root: str | None = None,
) -> ZenoProofVerifyResult:
    errors: list[str] = []
    verifier_index, claim_index, registry_errors = _registry_indexes(registry)
    errors.extend(f"registry:{error}" for error in registry_errors)

    _unknown_fields(artifact, allowed=ARTIFACT_KEYS, label="artifact", errors=errors)
    if artifact.get("schema") != ARTIFACT_SCHEMA:
        errors.append("artifact_schema_mismatch")

    proof_id = _require_hash(artifact, "proof_id", errors)
    claim_id = _require_hash(artifact, "claim_id", errors)
    verifier_id = _require_hash(artifact, "verifier_id", errors)
    statement_hash = _require_hash(artifact, "statement_hash", errors)
    assumptions_hash = _require_hash(artifact, "assumptions_hash", errors)
    input_root = _require_hash(artifact, "input_commitment_root", errors)
    output_root = _require_hash(artifact, "output_commitment_root", errors)
    verifier_policy_root = _require_hash(artifact, "verifier_policy_root", errors)
    toolchain_id = _require_hash(artifact, "toolchain_id", errors)
    issued_at = _require_int_epoch(artifact, "issued_at_epoch", errors)
    expires_at = _require_int_epoch(artifact, "expires_at_epoch", errors)
    _str_list(artifact.get("non_claims"), label="artifact_non_claims", errors=errors)

    proof_kind_raw = artifact.get("proof_kind")
    proof_kind = proof_kind_raw if isinstance(proof_kind_raw, str) else None
    if proof_kind not in SUPPORTED_PROOF_KINDS:
        errors.append("proof_kind_invalid")
    if artifact.get("result") != "accepted":
        errors.append("artifact_result_not_accepted")

    if proof_id is not None:
        try:
            expected_proof_id = artifact_content_hash(artifact)
        except (TypeError, ValueError):
            expected_proof_id = None
            errors.append(f"proof_id_content_hash_unencodable:{proof_id}")
        if expected_proof_id is not None and proof_id != expected_proof_id:
            errors.append("proof_id_content_hash_mismatch")

    if issued_at is not None and expires_at is not None and expires_at < issued_at:
        errors.append("artifact_expires_before_issued")
    if issued_at is not None and now_epoch < issued_at:
        errors.append("artifact_from_future")
    if expires_at is not None and now_epoch > expires_at:
        errors.append("artifact_expired")

    claim = claim_index.get(claim_id or "")
    evidence_class: str | None = None
    if claim is None:
        errors.append("claim_not_registered")
    else:
        evidence_class = str(claim.get("evidence_class"))
        if statement_hash is not None and statement_hash != claim.get("statement_hash"):
            errors.append("claim_statement_hash_mismatch")
        if assumptions_hash is not None and assumptions_hash != claim.get("assumptions_hash"):
            errors.append("claim_assumptions_hash_mismatch")

    verifier = verifier_index.get(verifier_id or "")
    if verifier is None:
        errors.append("verifier_not_registered")
    else:
        if verifier.get("revoked") is True:
            errors.append("verifier_revoked")
        if verifier_policy_root is not None and verifier_policy_root != verifier.get("current_policy_root"):
            errors.append("verifier_policy_root_stale")
        proof_kinds = _str_list(verifier.get("proof_kinds"), label="verifier_proof_kinds", errors=errors)
        if proof_kind is not None and proof_kind not in proof_kinds:
            errors.append("proof_kind_not_allowed")
        toolchains = _str_list(verifier.get("toolchain_ids"), label="verifier_toolchain_ids", errors=errors)
        if toolchain_id is not None and toolchain_id not in toolchains:
            errors.append("toolchain_not_allowed")
        _run_external_verifier_if_needed(artifact, verifier, errors)

    if expected_claim_id is not None and claim_id != expected_claim_id:
        errors.append("expected_claim_id_mismatch")
    if expected_input_commitment_root is not None and input_root != expected_input_commitment_root:
        errors.append("expected_input_commitment_root_mismatch")
    if expected_output_commitment_root is not None and output_root != expected_output_commitment_root:
        errors.append("expected_output_commitment_root_mismatch")

    proof_errors = [
        error
        for error in errors
        if not error.startswith("registry:")
        and error
        not in {
            "expected_claim_id_mismatch",
            "expected_input_commitment_root_mismatch",
            "expected_output_commitment_root_mismatch",
            "claim_statement_hash_mismatch",
            "claim_assumptions_hash_mismatch",
            "claim_not_registered",
            "verifier_not_registered",
            "verifier_revoked",
            "verifier_policy_root_stale",
            "proof_kind_not_allowed",
            "toolchain_not_allowed",
            "artifact_from_future",
            "artifact_expired",
            "artifact_expires_before_issued",
        }
    ]
    binding_errors = [
        error
        for error in errors
        if error
        in {
            "expected_claim_id_mismatch",
            "expected_input_commitment_root_mismatch",
            "expected_output_commitment_root_mismatch",
            "claim_statement_hash_mismatch",
            "claim_assumptions_hash_mismatch",
            "claim_not_registered",
        }
    ]
    policy_errors = [
        error
        for error in errors
        if error.startswith("registry:")
        or error
        in {
            "verifier_not_registered",
            "verifier_revoked",
            "verifier_policy_root_stale",
            "proof_kind_not_allowed",
            "toolchain_not_allowed",
        }
    ]
    freshness_errors = [
        error
        for error in errors
        if error in {"artifact_from_future", "artifact_expired", "artifact_expires_before_issued"}
    ]
    return ZenoProofVerifyResult(
        status="rejected" if errors else "accepted",
        errors=errors,
        proof_ok=not proof_errors,
        binding_ok=not binding_errors,
        policy_ok=not policy_errors,
        freshness_ok=not freshness_errors,
        claim_id=claim_id,
        proof_id=proof_id,
        verifier_id=verifier_id,
        evidence_class=evidence_class,
    )


def _run_external_verifier_if_needed(
    artifact: Mapping[str, Any],
    verifier: Mapping[str, Any],
    errors: list[str],
) -> None:
    mode = verifier.get("execution_mode")
    if mode == "local_static_accept":
        return
    if mode != "subprocess_json":
        errors.append("verifier_execution_mode_invalid")
        return
    command = verifier.get("verifier_command")
    if not isinstance(command, list) or not command or not all(isinstance(item, str) and item for item in command):
        errors.append("verifier_command_invalid")
        return
    timeout_ms = verifier.get("timeout_ms")
    max_input_bytes = verifier.get("max_input_bytes")
    allow_path_lookup = verifier.get("allow_path_lookup")
    if not isinstance(timeout_ms, int) or isinstance(timeout_ms, bool) or timeout_ms <= 0:
        errors.append("verifier_timeout_ms_invalid")
        return
    if not isinstance(max_input_bytes, int) or isinstance(max_input_bytes, bool) or max_input_bytes <= 0:
        errors.append("verifier_max_input_bytes_invalid")
        return
    if max_input_bytes > MAX_JSON_BYTES:
        errors.append("verifier_max_input_bytes_too_large")
        return
    if not isinstance(allow_path_lookup, bool):
        errors.append("verifier_allow_path_lookup_invalid")
        return
    proof_verifier = make_proof_verifier(
        ProofVerifierConfig(
            enabled=True,
            verifier_cmd=command,
            allow_path_lookup=allow_path_lookup,
            timeout_s=float(timeout_ms) / 1000.0,
            max_proof_bytes=int(max_input_bytes),
        )
    )
    ok, error = proof_verifier.verify(artifact)
    if not ok:
        errors.append(f"external_verifier_failed:{error or 'proof rejected'}")


def verify_o5_independence_witness(
    witness: Mapping[str, Any],
    registry: Mapping[str, Any],
    *,
    primary_artifact: Mapping[str, Any],
    now_epoch: int,
    expected_input_commitment_root: str | None,
    expected_output_commitment_root: str | None,
) -> O5IndependenceWitnessResult:
    errors: list[str] = []
    _, claim_index, registry_errors = _registry_indexes(registry)
    errors.extend(f"registry:{error}" for error in registry_errors)

    _unknown_fields(witness, allowed=O5_INDEPENDENCE_WITNESS_KEYS, label="o5_witness", errors=errors)
    if witness.get("schema") != O5_INDEPENDENCE_WITNESS_SCHEMA:
        errors.append("o5_witness_schema_mismatch")
    witness_id = _require_hash(witness, "witness_id", errors)
    if witness_id is not None:
        try:
            expected_witness_id = o5_independence_witness_content_hash(witness)
        except (TypeError, ValueError):
            expected_witness_id = None
            errors.append(f"o5_witness_hash_unencodable:{witness_id}")
        if expected_witness_id is not None and witness_id != expected_witness_id:
            errors.append("o5_witness_hash_mismatch")

    primary_proof_id = _require_hash(witness, "primary_proof_id", errors)
    primary_claim_id = _require_hash(witness, "primary_claim_id", errors)
    witness_input_root = _require_hash(witness, "expected_input_commitment_root", errors)
    witness_output_root = _require_hash(witness, "expected_output_commitment_root", errors)
    _str_list(witness.get("non_claims"), label="o5_witness_non_claims", errors=errors)

    required_verifiers = _require_int_epoch(witness, "required_distinct_verifier_count", errors)
    required_kinds = _require_int_epoch(witness, "required_distinct_proof_kind_count", errors)
    if required_verifiers is not None and required_verifiers < 2:
        errors.append("required_distinct_verifier_count_must_be_at_least_2")
    if required_kinds is not None and required_kinds < 2:
        errors.append("required_distinct_proof_kind_count_must_be_at_least_2")
    if (
        expected_input_commitment_root is not None
        and witness_input_root is not None
        and witness_input_root != expected_input_commitment_root
    ):
        errors.append("o5_witness_expected_input_root_mismatch")
    if (
        expected_output_commitment_root is not None
        and witness_output_root is not None
        and witness_output_root != expected_output_commitment_root
    ):
        errors.append("o5_witness_expected_output_root_mismatch")

    primary_result = verify_zenoproof_artifact(
        primary_artifact,
        registry,
        now_epoch=now_epoch,
        expected_input_commitment_root=expected_input_commitment_root,
        expected_output_commitment_root=expected_output_commitment_root,
    )
    if primary_result.status != "accepted":
        errors.append("primary_artifact_not_accepted")
        errors.extend(f"primary:{error}" for error in primary_result.errors)
    if primary_result.evidence_class != "O5":
        errors.append("primary_claim_must_be_o5")
    if primary_proof_id is not None and primary_proof_id != primary_artifact.get("proof_id"):
        errors.append("primary_proof_id_mismatch")
    if primary_claim_id is not None and primary_claim_id != primary_artifact.get("claim_id"):
        errors.append("primary_claim_id_mismatch")

    crosschecks_raw = witness.get("crosscheck_proof_artifacts")
    crosschecks: list[Mapping[str, Any]] = []
    if not isinstance(crosschecks_raw, list) or not crosschecks_raw:
        errors.append("crosscheck_proof_artifacts_must_be_nonempty_list")
    elif len(crosschecks_raw) > 16:
        errors.append("crosscheck_proof_artifacts_too_many")
    else:
        for pos, artifact in enumerate(crosschecks_raw):
            if not isinstance(artifact, Mapping):
                errors.append(f"crosscheck_{pos}_must_be_object")
                continue
            crosschecks.append(artifact)

    verifier_ids: set[str] = set()
    proof_kinds: set[str] = set()
    claim_ids: set[str] = set()
    proof_ids: set[str] = set()
    primary_claim = primary_result.claim_id
    primary_claim_deps: set[str] = set()
    if primary_claim is not None:
        claim_ids.add(primary_claim)
        claim = claim_index.get(primary_claim)
        deps = claim.get("dependency_claim_ids") if isinstance(claim, Mapping) else None
        if isinstance(deps, list):
            primary_claim_deps = {dep for dep in deps if isinstance(dep, str)}
    if isinstance(primary_artifact.get("verifier_id"), str):
        verifier_ids.add(str(primary_artifact["verifier_id"]))
    if isinstance(primary_artifact.get("proof_kind"), str):
        proof_kinds.add(str(primary_artifact["proof_kind"]))
    if isinstance(primary_artifact.get("proof_id"), str):
        proof_ids.add(str(primary_artifact["proof_id"]))

    for pos, artifact in enumerate(crosschecks):
        result = verify_zenoproof_artifact(
            artifact,
            registry,
            now_epoch=now_epoch,
            expected_input_commitment_root=expected_input_commitment_root,
            expected_output_commitment_root=expected_output_commitment_root,
        )
        if result.status != "accepted":
            errors.append(f"crosscheck_artifact_not_accepted:{pos}")
            errors.extend(f"crosscheck_{pos}:{error}" for error in result.errors)
        if result.evidence_class not in {"O4", "O5"}:
            errors.append(f"crosscheck_claim_must_be_o4_or_o5:{pos}")
        if result.claim_id is not None:
            if result.claim_id == primary_claim:
                errors.append(f"crosscheck_claim_must_differ_from_primary:{pos}")
            if result.claim_id not in primary_claim_deps:
                errors.append(f"primary_claim_missing_crosscheck_dependency:{result.claim_id}")
            claim_ids.add(result.claim_id)
        if result.proof_id is not None:
            if result.proof_id in proof_ids:
                errors.append(f"duplicate_o5_proof_id:{result.proof_id}")
            proof_ids.add(result.proof_id)
        if result.verifier_id is not None:
            verifier_ids.add(result.verifier_id)
        proof_kind = artifact.get("proof_kind")
        if isinstance(proof_kind, str):
            proof_kinds.add(proof_kind)

    if required_verifiers is not None and len(verifier_ids) < required_verifiers:
        errors.append("distinct_verifier_count_below_required")
    if required_kinds is not None and len(proof_kinds) < required_kinds:
        errors.append("distinct_proof_kind_count_below_required")

    return O5IndependenceWitnessResult(
        status="rejected" if errors else "accepted",
        errors=errors,
        primary_claim_id=primary_result.claim_id,
        primary_proof_id=primary_result.proof_id,
        crosscheck_count=len(crosschecks),
        distinct_verifier_count=len(verifier_ids),
        distinct_proof_kind_count=len(proof_kinds),
        claim_ids=sorted(claim_ids),
    )


def oracle_o4_bridge_content_hash(bridge: Mapping[str, Any]) -> str:
    return sha256_json({key: value for key, value in bridge.items() if key != "bridge_id"})


def verify_oracle_o4_bridge(
    bridge: Mapping[str, Any],
    registry: Mapping[str, Any],
    *,
    now_epoch: int,
) -> OracleO4BridgeResult:
    errors: list[str] = []
    o5_witness_result: O5IndependenceWitnessResult | None = None
    _unknown_fields(bridge, allowed=ORACLE_BRIDGE_KEYS, label="oracle_o4_bridge", errors=errors)
    if bridge.get("schema") != ORACLE_BRIDGE_SCHEMA:
        errors.append("oracle_o4_bridge_schema_mismatch")
    bridge_id = _require_hash(bridge, "bridge_id", errors)
    if bridge_id is not None:
        try:
            expected_bridge_id = oracle_o4_bridge_content_hash(bridge)
        except (TypeError, ValueError):
            expected_bridge_id = None
            errors.append(f"oracle_o4_bridge_hash_unencodable:{bridge_id}")
        if expected_bridge_id is not None and bridge_id != expected_bridge_id:
            errors.append("oracle_o4_bridge_hash_mismatch")

    bundle = bridge.get("receipt_bundle")
    if not isinstance(bundle, Mapping):
        errors.append("receipt_bundle_must_be_object")
        receipt_result = None
    else:
        receipt_result = verify_bundle(bundle)
        if receipt_result.status != "accepted":
            errors.append("o3_receipt_not_accepted")
            errors.extend(f"receipt:{error}" for error in receipt_result.errors)

    proof_artifact = bridge.get("proof_artifact")
    if not isinstance(proof_artifact, Mapping):
        errors.append("proof_artifact_must_be_object")
        proof_result = None
    else:
        expected_input = (
            oracle_o4_input_root(bundle)
            if isinstance(bundle, Mapping) and receipt_result and receipt_result.status == "accepted"
            else None
        )
        proof_result = verify_zenoproof_artifact(
            proof_artifact,
            registry,
            now_epoch=now_epoch,
            expected_input_commitment_root=expected_input,
        )
        if proof_result.status != "accepted":
            errors.append("zenoproof_artifact_not_accepted")
            errors.extend(f"proof:{error}" for error in proof_result.errors)
        if proof_result.evidence_class not in {"O4", "O5"}:
            errors.append("zenoproof_claim_must_be_o4_or_o5")

    target = bridge.get("target_evidence_class")
    if target not in {"O4", "O5"}:
        errors.append("target_evidence_class_must_be_o4_or_o5")
    if target == "O5" and proof_result is not None and proof_result.evidence_class != "O5":
        errors.append("o5_bridge_requires_o5_claim")
    if target == "O5":
        witness = bridge.get("o5_independence_witness")
        if not isinstance(witness, Mapping):
            errors.append("o5_independence_witness_required")
        elif isinstance(proof_artifact, Mapping):
            expected_input = (
                oracle_o4_input_root(bundle)
                if isinstance(bundle, Mapping) and receipt_result and receipt_result.status == "accepted"
                else None
            )
            expected_output = (
                str(proof_artifact.get("output_commitment_root"))
                if _is_hash(proof_artifact.get("output_commitment_root"))
                else None
            )
            o5_witness_result = verify_o5_independence_witness(
                witness,
                registry,
                primary_artifact=proof_artifact,
                now_epoch=now_epoch,
                expected_input_commitment_root=expected_input,
                expected_output_commitment_root=expected_output,
            )
            if o5_witness_result.status != "accepted":
                errors.append("o5_independence_witness_not_accepted")
                errors.extend(f"o5_witness:{error}" for error in o5_witness_result.errors)
    elif bridge.get("o5_independence_witness") is not None:
        errors.append("o5_independence_witness_only_for_o5_bridge")

    return OracleO4BridgeResult(
        status="rejected" if errors else "accepted",
        errors=errors,
        receipt_status=None if receipt_result is None else receipt_result.status,
        proof_status=None if proof_result is None else proof_result.status,
        o5_witness_status=None if o5_witness_result is None else o5_witness_result.status,
        query_id=None if receipt_result is None else receipt_result.query_id,
        value_hash=None if receipt_result is None else receipt_result.value_hash,
        consumer_module=None if receipt_result is None else receipt_result.consumer_module,
        action_kind=None if receipt_result is None else receipt_result.action_kind,
        action_id=None if receipt_result is None else receipt_result.action_id,
        proof_id=None if proof_result is None else proof_result.proof_id,
        claim_id=None if proof_result is None else proof_result.claim_id,
        target_evidence_class=target if isinstance(target, str) else None,
    )


def verify_reward_gate(
    reward_gate: Mapping[str, Any],
    registry: Mapping[str, Any],
    *,
    now_epoch: int,
) -> ZenoProofRewardGateResult:
    errors: list[str] = []
    _unknown_fields(reward_gate, allowed=REWARD_GATE_KEYS, label="reward_gate", errors=errors)
    if reward_gate.get("schema") != REWARD_GATE_SCHEMA:
        errors.append("reward_gate_schema_mismatch")

    previous_claim_ids = _str_list(
        reward_gate.get("previously_rewarded_claim_ids"),
        label="previously_rewarded_claim_ids",
        errors=errors,
    )
    for claim_id in previous_claim_ids:
        if not _is_hash(claim_id):
            errors.append(f"previously_rewarded_claim_id_must_be_sha256:{claim_id}")

    reward_pool_before = _require_reward_amount(reward_gate, "reward_pool_before_e8", errors)
    reward_amount = _require_reward_amount(reward_gate, "reward_amount_e8", errors)
    reward_pool_after = _require_reward_amount(reward_gate, "reward_pool_after_e8", errors)

    proof_artifact = reward_gate.get("proof_artifact")
    if not isinstance(proof_artifact, Mapping):
        errors.append("proof_artifact_must_be_object")
        proof_result = None
    else:
        proof_result = verify_zenoproof_artifact(
            proof_artifact,
            registry,
            now_epoch=now_epoch,
            expected_claim_id=reward_gate.get("expected_claim_id"),
            expected_input_commitment_root=reward_gate.get("expected_input_commitment_root"),
            expected_output_commitment_root=reward_gate.get("expected_output_commitment_root"),
        )
        if proof_result.status != "accepted":
            errors.append("zenoproof_artifact_not_accepted")
            errors.extend(f"proof:{error}" for error in proof_result.errors)

    if reward_pool_before is not None and reward_pool_after is not None and reward_pool_after > reward_pool_before:
        errors.append("reward_pool_after_exceeds_before")
    if None not in (reward_pool_before, reward_amount, reward_pool_after):
        assert reward_pool_before is not None
        assert reward_amount is not None
        assert reward_pool_after is not None
        if reward_amount == 0:
            errors.append("reward_amount_must_be_positive")
        if reward_amount > reward_pool_before:
            errors.append("reward_amount_exceeds_pool")
        if reward_amount != reward_pool_before - reward_pool_after:
            errors.append("reward_amount_mismatch")

    claim_id = None if proof_result is None else proof_result.claim_id
    proof_id = None if proof_result is None else proof_result.proof_id
    unique_claim = bool(claim_id is not None and claim_id not in previous_claim_ids)
    if claim_id is not None and claim_id in previous_claim_ids:
        errors.append("claim_already_rewarded")

    checks = {
        "proof_ok": bool(proof_result is not None and proof_result.proof_ok),
        "binding_ok": bool(proof_result is not None and proof_result.binding_ok),
        "policy_ok": bool(proof_result is not None and proof_result.policy_ok),
        "freshness_ok": bool(proof_result is not None and proof_result.freshness_ok),
        "unique_claim": unique_claim,
        "reward_pool_has_budget": bool(
            reward_pool_before is not None
            and reward_amount is not None
            and reward_pool_after is not None
            and reward_amount > 0
            and reward_amount <= reward_pool_before
            and reward_amount == reward_pool_before - reward_pool_after
        ),
    }
    return ZenoProofRewardGateResult(
        status="rejected" if errors else "accepted",
        errors=errors,
        checks=checks,
        claim_id=claim_id,
        proof_id=proof_id,
        reward_amount_e8=reward_amount,
        reward_pool_before_e8=reward_pool_before,
        reward_pool_after_e8=reward_pool_after,
    )


def _load_json(path: Path) -> Mapping[str, Any]:
    if path.stat().st_size > MAX_JSON_BYTES:
        raise ValueError(f"json_file_too_large:{path}")
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError("json root must be an object")
    return obj


def _write_json(payload: Mapping[str, Any], output: str | None) -> None:
    text = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if output:
        Path(output).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)


def cmd_sample_registry(args: argparse.Namespace) -> int:
    _write_json(sample_registry(), args.output)
    return 0


def cmd_sample_artifact(args: argparse.Namespace) -> int:
    _write_json(sample_artifact(), args.output)
    return 0


def cmd_sample_public_replay_artifact(args: argparse.Namespace) -> int:
    _write_json(sample_public_replay_artifact(args.profile), args.output)
    return 0


def cmd_sample_oracle_bridge(args: argparse.Namespace) -> int:
    _write_json(sample_oracle_o4_bridge(), args.output)
    return 0


def cmd_sample_oracle_o5_bridge(args: argparse.Namespace) -> int:
    _write_json(sample_oracle_o5_bridge(), args.output)
    return 0


def cmd_sample_reward_gate(args: argparse.Namespace) -> int:
    _write_json(sample_reward_gate(), args.output)
    return 0


def cmd_verify_registry(args: argparse.Namespace) -> int:
    try:
        registry = _load_json(Path(args.registry))
    except Exception as exc:
        _write_json(
            {
                "schema": "zenodex.zenoproof.registry_verify_result.v0",
                "ok": False,
                "status": "inconclusive",
                "errors": [f"load_failed:{exc}"],
            },
            args.output,
        )
        return 3
    errors = verify_registry_manifest(registry)
    _write_json(
        {
            "schema": "zenodex.zenoproof.registry_verify_result.v0",
            "ok": not errors,
            "status": "accepted" if not errors else "rejected",
            "errors": errors,
        },
        args.output,
    )
    return 0 if not errors else 2


def cmd_verify(args: argparse.Namespace) -> int:
    try:
        artifact = _load_json(Path(args.artifact))
        registry = _load_json(Path(args.registry))
    except Exception as exc:
        result = ZenoProofVerifyResult(
            status="inconclusive",
            errors=[f"load_failed:{exc}"],
            proof_ok=False,
            binding_ok=False,
            policy_ok=False,
            freshness_ok=False,
        )
        _write_json(result.to_json_obj(), args.output)
        return 3
    result = verify_zenoproof_artifact(
        artifact,
        registry,
        now_epoch=int(args.now_epoch),
        expected_claim_id=args.expected_claim_id,
        expected_input_commitment_root=args.expected_input_commitment_root,
        expected_output_commitment_root=args.expected_output_commitment_root,
    )
    _write_json(result.to_json_obj(), args.output)
    return 0 if result.status == "accepted" else 2


def cmd_verify_oracle_bridge(args: argparse.Namespace) -> int:
    try:
        bridge = _load_json(Path(args.bridge))
        registry = _load_json(Path(args.registry))
    except Exception as exc:
        result = OracleO4BridgeResult(status="inconclusive", errors=[f"load_failed:{exc}"])
        _write_json(result.to_json_obj(), args.output)
        return 3
    result = verify_oracle_o4_bridge(bridge, registry, now_epoch=int(args.now_epoch))
    _write_json(result.to_json_obj(), args.output)
    return 0 if result.status == "accepted" else 2


def cmd_verify_o5_witness(args: argparse.Namespace) -> int:
    try:
        witness = _load_json(Path(args.witness))
        primary_artifact = _load_json(Path(args.primary_artifact))
        registry = _load_json(Path(args.registry))
    except Exception as exc:
        result = O5IndependenceWitnessResult(status="inconclusive", errors=[f"load_failed:{exc}"])
        _write_json(result.to_json_obj(), args.output)
        return 3
    result = verify_o5_independence_witness(
        witness,
        registry,
        primary_artifact=primary_artifact,
        now_epoch=int(args.now_epoch),
        expected_input_commitment_root=args.expected_input_commitment_root,
        expected_output_commitment_root=args.expected_output_commitment_root,
    )
    _write_json(result.to_json_obj(), args.output)
    return 0 if result.status == "accepted" else 2


def cmd_verify_reward_gate(args: argparse.Namespace) -> int:
    try:
        reward_gate = _load_json(Path(args.reward_gate))
        registry = _load_json(Path(args.registry))
    except Exception as exc:
        result = ZenoProofRewardGateResult(
            status="inconclusive",
            errors=[f"load_failed:{exc}"],
            checks={
                "proof_ok": False,
                "binding_ok": False,
                "policy_ok": False,
                "freshness_ok": False,
                "unique_claim": False,
                "reward_pool_has_budget": False,
            },
        )
        _write_json(result.to_json_obj(), args.output)
        return 3
    result = verify_reward_gate(reward_gate, registry, now_epoch=int(args.now_epoch))
    _write_json(result.to_json_obj(), args.output)
    return 0 if result.status == "accepted" else 2


def cmd_self_test(args: argparse.Namespace) -> int:
    try:
        registry = _load_json(Path(args.registry)) if args.registry else sample_registry()
    except Exception as exc:
        receipt = {
            "schema": "zenodex.zenoproof.self_test.v0",
            "ok": False,
            "registry_errors": [f"load_failed:{exc}"],
            "artifact_result": None,
            "oracle_bridge_result": None,
            "reward_gate_result": None,
        }
        _write_json(receipt, args.output)
        return 3
    registry_errors = verify_registry_manifest(registry)
    artifact = sample_artifact()
    artifact_result = verify_zenoproof_artifact(artifact, registry, now_epoch=150)
    bridge = sample_oracle_o4_bridge()
    bridge_result = verify_oracle_o4_bridge(bridge, registry, now_epoch=150)
    o5_bridge = sample_oracle_o5_bridge()
    o5_bridge_result = verify_oracle_o4_bridge(o5_bridge, registry, now_epoch=150)
    reward_result = verify_reward_gate(sample_reward_gate(), registry, now_epoch=150)
    public_replay_results = {
        profile: verify_zenoproof_artifact(
            sample_public_replay_artifact(profile),
            registry,
            now_epoch=150,
        )
        for profile in PUBLIC_REPLAY_PROFILE_CONFIGS
    }
    receipt = {
        "schema": "zenodex.zenoproof.self_test.v0",
        "ok": (
            not registry_errors
            and artifact_result.status == "accepted"
            and bridge_result.status == "accepted"
            and o5_bridge_result.status == "accepted"
            and reward_result.status == "accepted"
            and all(result.status == "accepted" for result in public_replay_results.values())
        ),
        "registry_errors": registry_errors,
        "artifact_result": artifact_result.to_json_obj(),
        "oracle_bridge_result": bridge_result.to_json_obj(),
        "oracle_o5_bridge_result": o5_bridge_result.to_json_obj(),
        "reward_gate_result": reward_result.to_json_obj(),
        "public_replay_results": {
            profile: result.to_json_obj() for profile, result in public_replay_results.items()
        },
    }
    _write_json(receipt, args.output)
    return 0 if receipt["ok"] else 2


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="cmd", required=True)

    sample_registry_cmd = sub.add_parser("sample-registry", help="emit the sample verifier registry")
    sample_registry_cmd.add_argument("--output")
    sample_registry_cmd.set_defaults(func=cmd_sample_registry)

    sample_artifact_cmd = sub.add_parser("sample-artifact", help="emit a sample accepted ZenoProof artifact")
    sample_artifact_cmd.add_argument("--output")
    sample_artifact_cmd.set_defaults(func=cmd_sample_artifact)

    sample_public_replay_cmd = sub.add_parser(
        "sample-public-replay-artifact",
        help="emit a sample public replay ZenoProof artifact",
    )
    sample_public_replay_cmd.add_argument("--profile", choices=tuple(PUBLIC_REPLAY_PROFILE_CONFIGS), default=PUBLIC_REPLAY_PROFILE)
    sample_public_replay_cmd.add_argument("--output")
    sample_public_replay_cmd.set_defaults(func=cmd_sample_public_replay_artifact)

    sample_bridge_cmd = sub.add_parser("sample-oracle-bridge", help="emit a sample Oracle O4 bridge")
    sample_bridge_cmd.add_argument("--output")
    sample_bridge_cmd.set_defaults(func=cmd_sample_oracle_bridge)

    sample_o5_bridge_cmd = sub.add_parser("sample-oracle-o5-bridge", help="emit a sample Oracle O5 bridge")
    sample_o5_bridge_cmd.add_argument("--output")
    sample_o5_bridge_cmd.set_defaults(func=cmd_sample_oracle_o5_bridge)

    sample_reward_cmd = sub.add_parser("sample-reward-gate", help="emit a sample ZenoProof reward gate")
    sample_reward_cmd.add_argument("--output")
    sample_reward_cmd.set_defaults(func=cmd_sample_reward_gate)

    registry_cmd = sub.add_parser("verify-registry", help="verify a ZenoProof registry manifest")
    registry_cmd.add_argument("--registry", required=True)
    registry_cmd.add_argument("--output")
    registry_cmd.set_defaults(func=cmd_verify_registry)

    verify_cmd = sub.add_parser("verify", help="verify one ZenoProof artifact")
    verify_cmd.add_argument("--artifact", required=True)
    verify_cmd.add_argument("--registry", required=True)
    verify_cmd.add_argument("--now-epoch", type=int, default=150)
    verify_cmd.add_argument("--expected-claim-id")
    verify_cmd.add_argument("--expected-input-commitment-root")
    verify_cmd.add_argument("--expected-output-commitment-root")
    verify_cmd.add_argument("--output")
    verify_cmd.set_defaults(func=cmd_verify)

    bridge_cmd = sub.add_parser("verify-oracle-bridge", help="verify an Oracle O4/O5 bridge")
    bridge_cmd.add_argument("--bridge", required=True)
    bridge_cmd.add_argument("--registry", required=True)
    bridge_cmd.add_argument("--now-epoch", type=int, default=150)
    bridge_cmd.add_argument("--output")
    bridge_cmd.set_defaults(func=cmd_verify_oracle_bridge)

    o5_witness_cmd = sub.add_parser("verify-o5-witness", help="verify a ZenoProof O5 independence witness")
    o5_witness_cmd.add_argument("--witness", required=True)
    o5_witness_cmd.add_argument("--primary-artifact", required=True)
    o5_witness_cmd.add_argument("--registry", required=True)
    o5_witness_cmd.add_argument("--now-epoch", type=int, default=150)
    o5_witness_cmd.add_argument("--expected-input-commitment-root")
    o5_witness_cmd.add_argument("--expected-output-commitment-root")
    o5_witness_cmd.add_argument("--output")
    o5_witness_cmd.set_defaults(func=cmd_verify_o5_witness)

    reward_cmd = sub.add_parser("verify-reward-gate", help="verify a ZenoProof proof-mining reward gate")
    reward_cmd.add_argument("--reward-gate", required=True)
    reward_cmd.add_argument("--registry", required=True)
    reward_cmd.add_argument("--now-epoch", type=int, default=150)
    reward_cmd.add_argument("--output")
    reward_cmd.set_defaults(func=cmd_verify_reward_gate)

    self_test_cmd = sub.add_parser("self-test", help="run the built-in ZenoProof v0 replay check")
    self_test_cmd.add_argument("--registry")
    self_test_cmd.add_argument("--output")
    self_test_cmd.set_defaults(func=cmd_self_test)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
