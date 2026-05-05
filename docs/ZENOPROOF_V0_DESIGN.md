# ZenoProof v0 Design

Status: local verifier shell for O4/O5 evidence. A live proof network remains
out of scope for v0.

ZenoProof is the proof registry and verifier layer that lets ZenoOracle and
ZenoDEX consume proof-backed evidence without trusting arbitrary proof-looking
objects. O3 remains receipt-backed oracle evidence. O4 adds proof-backed
provenance or computation. O5 adds independent cross-checking across mechanisms.

## Core Rule

```text
ProofAccepted -> VerifierWhitelisted and ArtifactBound and PolicyCurrent and Fresh
```

A proof object is usable only when an authorized verifier checked it, the proof
binds to the intended claim and inputs, the verifier policy is current, and the
proof is fresh enough for its consumer.

## Objects

### ProofArtifact

Minimum fields:

```json
{
  "schema": "zenodex.zenoproof.artifact.v0",
  "proof_id": "sha256:...",
  "proof_kind": "lean|tla|esso|risc0|smt|morph_bundle|julia_witness|public_replay",
  "claim_id": "sha256:...",
  "statement_hash": "sha256:...",
  "assumptions_hash": "sha256:...",
  "input_commitment_root": "sha256:...",
  "output_commitment_root": "sha256:...",
  "verifier_id": "sha256:...",
  "verifier_policy_root": "sha256:...",
  "toolchain_id": "sha256:...",
  "issued_at_epoch": 0,
  "expires_at_epoch": 0,
  "result": "accepted",
  "non_claims": []
}
```

The artifact hash must cover every field except `proof_id`, which is the
content hash of the body.

### VerifierRegistry

Tracks authorized verifiers and their scope:

- verifier ID;
- proof kinds allowed;
- image ID or executable hash;
- toolchain version;
- max input size;
- max runtime or deterministic resource bound;
- policy epoch;
- revocation state.

Host code verifies cryptographic receipts and tool outputs. Tau/ESSO gates
consume only derived booleans such as `proof_ok`, `binding_ok`, `policy_ok`,
and `freshness_ok`.

### ClaimDAG

Claims form a dependency graph:

```text
claim -> assumptions -> evidence artifacts -> verifier policy
```

Each promoted claim must preserve:

- explicit assumptions;
- dependency closure;
- non-claims;
- replay command;
- evidence class.

Cycles, missing dependencies, stale verifier policies, and unknown proof kinds
fail closed.

## Verifier API

The first host verifier API should accept a canonical JSON object and return a
canonical JSON result:

```json
{
  "schema": "zenodex.zenoproof.verify_result.v0",
  "ok": true,
  "proof_ok": true,
  "binding_ok": true,
  "policy_ok": true,
  "freshness_ok": true,
  "claim_id": "sha256:...",
  "proof_id": "sha256:...",
  "verifier_id": "sha256:...",
  "errors": []
}
```

Existing plumbing in `src/integration/proof_verifier.py` is the subprocess
boundary to reuse for early local verifiers. It already fails closed on
disabled, misconfigured, timeout, oversize, malformed, and bad-exit paths.

### PublicReplayVerifier

`tools/zenoproof_public_replay_verifier.py` provides the first non-static
verifier roots in the v0 registry. It accepts a ZenoProof artifact only when
the artifact binds to an allowed public replay profile and the profile's public
replay command returns an accepted receipt.

```bash
python3 tools/zeno_oracle_workflow_evidence_status.py --format json
julia tools/zeno_oracle_math_witness_sweep.jl --json
cd lean-mathlib && lake env lean Proofs/ZenoOracleMathWitness.lean
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q -p no:cacheprovider tests/formal/test_tla_oracle_recovery_lifecycle.py
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q -p no:cacheprovider tests/formal/test_oracle_recovery_ltlf.py
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q -p no:cacheprovider tests/formal/test_esso_zusd_oracle_recovery_lifecycle_v1.py
python3 -c 'from tools.zeno_oracle_workflow_evidence_status import build_morph_oracle_clamp_envelope_status; import json; print(json.dumps(build_morph_oracle_clamp_envelope_status(), sort_keys=True))'
python3 tools/zeno_oracle_smt_freshness_replay.py --format json
```

The verifier checks the profile claim ID, verifier ID, policy root, toolchain
ID, input commitment root, and output commitment root. The output root is the
canonical hash of the accepted profile receipt. For the Lean profile, the
receipt also requires a clean placeholder scan over the witness anchor and root
import file. For the TLA, LTLf, and ESSO profiles, the receipt is a normalized
wrapper around the corresponding public pytest replay command. For the Morph
profile, the receipt requires both `check` and `check2` to pass on the
oracle-clamp envelope domain. For the SMT profile, the receipt requires Z3 and
CVC5 to return `unsat` for each Oracle freshness safety query.

## Proof Mining Reward Gate

ZenoProof can use the existing `ZenoProofMining.submit_proof` path only after
the proof context is verified by the host.

Reward acceptance requires:

```text
proof_ok
and binding_ok
and policy_ok
and unique_claim
and reward_pool_has_budget
```

The no-minting default remains preferred: rewards come from a bounded pool, and
proof churn is rejected or unpaid when it does not add a new useful claim,
counterexample, or proof obligation.

`tools/zenoproof_reward_payout_replay.py` is the v0 local payout bridge. It
verifies an accepted ZenoProof reward gate, scales the e8 reward budget into the
bounded proof-mining model, builds an explicit `proof_mining_claim`, executes
the proof-mining manager packet, and runs the claimability gate against a
runtime-backed app-state snapshot.

The current replay uses `unit_scale_e8 = 1_000_000`, so the sample reward gate
maps `100_000_000 -> 100`, `25_000_000 -> 25`, and `75_000_000 -> 75` in the
bounded local manager. This is replay evidence for payout authorization logic.
It does not settle live tokens.

## Production Governance Policy Gate

`tools/check_zenoproof_production_governance_policy.py` is the first
production-candidate governance checker for the v0 shell. It verifies the
registry manifest structurally, quarantines `local_static_accept` verifiers as
devnet-only, enables only subprocess/public-replay verifier IDs for the
candidate production set, checks distinct proof-kind coverage, and binds the
registry to governance, code-signing, sandbox, revocation, O4/O5 bridge, and
reward-settlement controls.

```bash
python3 tools/check_zenoproof_production_governance_policy.py --format text
```

Current expected receipt:

```text
status = accepted
error_count = 0
go_live_blocker_count = 7
production_enabled_verifier_count = 8
distinct_proof_kind_count = 8
```

The live gate remains fail-closed:

```bash
python3 tools/check_zenoproof_production_governance_policy.py --require-live
```

This rejects with `go_live_blockers_present` until governance execution,
production verifier code signing, sandbox deployment, live revocation drill,
public proof-network soak, path-lookup removal for production verifiers, and
live proof-mining token settlement are backed by replayable evidence.

## Oracle O4/O5 Bridge

ZenoOracle may upgrade an accepted read from O3 to O4 only when a ZenoProof
artifact binds to the same query, value, source/admission set, registry roots,
consumer profile, and time window.

O5 requires independent mechanisms. Examples:

- admitted median aggregate plus independent prover-checked source provenance;
- accepted read plus independent cross-module sync proof;
- economic envelope plus independent Julia/Morph witness search showing no
  profitable attack under declared bounds.

The bridge rule is:

```text
O4OrO5OracleUseOK :=
  O3ReceiptOK
  and ZenoProofAccepted
  and SameQueryValueWindow
  and SameConsumerAction
```

The O3 receipt remains mandatory. Proof evidence strengthens the receipt; it
does not replace consumer-action binding.

For an O5 bridge, the bridge must also carry an
`o5_independence_witness`. The witness binds the primary O5 proof and each
cross-check proof to the same Oracle input root and output root, requires at
least two distinct verifier IDs and two distinct proof kinds, and verifies that
the primary O5 claim depends on the cross-check claim IDs in the registry DAG.
Missing witnesses, weak verifier/proof-kind diversity, duplicate proof IDs, bad
input/output roots, and missing DAG dependencies fail closed.

## Current v0 Shell

The repo-local v0 shell includes:

1. `tools/zenoproof_verify.py` for local artifact verification, registry
   validation, Oracle O4 bridge checking, and Oracle O5 independence-witness
   checking.
2. `tools/zenoproof_public_replay_verifier.py` for the workflow-evidence,
   Julia witness-sweep, Lean witness-anchor, TLA Oracle recovery, LTLf Oracle
   recovery, ESSO zUSD Oracle recovery, and Morph oracle-clamp public replay
   profiles, plus the SMT Oracle freshness public replay profile.
3. `tools/zenoproof_registry_manifest.json` for the public sample verifier
   policy and the first public replay verifier policies.
4. `tools/zenoproof_reward_payout_replay.py` for the bounded local bridge from
   an accepted ZenoProof reward gate into proof-mining claim construction,
   manager execution, and claimability checks.
5. `tests/test_zenoproof_verify.py` for malformed proof artifacts, stale
   verifier policy, wrong claim binding, unknown proof kind,
   timeout-as-success, wrong Oracle bridge binding, and proof-mining reward
   gate rejection.
6. `tests/test_zenoproof_reward_payout_replay.py` for the accepted bounded
   payout path and bad ZenoProof binding rejection.
7. `python3 tools/zenoproof_verify.py self-test --registry tools/zenoproof_registry_manifest.json`
   as the public replay command for the sample verifier shell, Oracle O4 bridge,
   Oracle O5 bridge, local reward gate, workflow-evidence public replay verifier, Julia
   witness-sweep public replay verifier, Lean witness-anchor public replay
   verifier, TLA public replay verifier, LTLf public replay verifier, and ESSO
   public replay verifier, Morph public replay verifier, and SMT public replay
   verifier.

The local reward gate accepts only when the ZenoProof artifact is accepted,
`proof_ok`, `binding_ok`, `policy_ok`, and `freshness_ok` are true, the claim
has not already been rewarded, and the reward pool transition is conservative:

```text
RewardAmount = RewardPoolBefore - RewardPoolAfter
```

Remaining production work: deepen the SMT, TLA, ESSO, Lean, Julia, and Morph
lanes beyond the current bounded anchors, promote the bounded local payout
replay to live proof-mining token settlement, execute production verifier
governance/revocation, and promote O4/O5 claims only when their replay commands
use public artifacts.
