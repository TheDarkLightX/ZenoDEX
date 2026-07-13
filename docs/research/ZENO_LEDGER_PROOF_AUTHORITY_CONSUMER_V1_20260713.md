# ZenoLedger Proof-Authority Consumer V1

Date: 2026-07-13
Status: restricted singleton V1 proof authority implemented; settlement and
production authority remain disabled

## Scope

This lane governs the final consumer of `proof_required` and
`bridge_policy.requires_proof_journal`. It separates three objects:

```text
proof metadata or verifier report
    -> diagnostic data only

governed proof-authority binding
    -> data-only policy identity committed by ledger state

private authenticated verifier result
    -> cryptographic result minted by the exact strict verifier
```

The positive authority decision requires the last two objects to agree on the
same policy, chain, profile, height range, authority manifest, registry, and
strict result schema. A JSON mapping containing `ok`, `header_bound`,
`risc0_verified`, or similar booleans cannot enter that join.

## Current V0 Result

The current V0 profile and replay configuration do not commit a proof-authority
policy ID. The consumer therefore returns:

```text
proof_authority_status = required_pending
proof_authority_satisfied = false
proof_authority_capable = false
```

It also emits the typed obligation
`zeno_ledger.proof_authority.consumer_binding.v1`, which names the missing
bindings:

- a private authenticated strict-verifier result;
- a consensus-bound authority-manifest SHA-256;
- a consensus-bound proof-authority policy ID;
- a consensus-bound verifier-registry ID;
- a replay-config digest when structural diagnostic mode has no replay config.

This replaces the prior ad hoc pending string with a deterministic typed
decision. The range verifier continues to reject proof-required V0 replay.
An explicitly selected V1 singleton path can satisfy proof authority through
the restricted state-domain bridge described below.

## Restricted Positive Port

`GovernedProofAuthorityBindingV1` defines the data-only policy surface:

```text
policy ID
chain ID
authority-manifest SHA-256
verifier-registry ID and entry ID
strict authenticated-result schema
proof profile
valid-from and optional valid-until heights
```

The policy ID is recomputed from canonical fields. The consumer rejects a
wrong policy, wrong chain/profile, a policy that is not yet valid, and a stale
policy before considering any verifier result.

The strict adapter executes one pinned verifier process and privately mints an
authenticated observation only after the complete response is rebound to the
governed manifest, registry, policy, header, proof metadata, proof envelope,
and replay config. The private observation has no public constructor and a
caller mapping cannot replace it.

The private seal prevents nominal and accidental construction. Arbitrary
hostile code running in the same Python interpreter can reach module-private
objects, so same-interpreter adversarial isolation is outside this claim. A
production deployment requires a process-isolated verifier-to-admission
handoff or a native unforgeable capability boundary.

The strict Spot verifier output schema is:

```text
zenodex.zeno_ledger.authenticated_spot_proof_facts.v1
```

It is expected to bind the authority manifest, registry and entry, chain,
height, canonical header, config, receipt security profile, exact receipt and
journal, Spot transaction commitment, and ZenoLedger transaction root. Its
own non-claims for ledger state-root equivalence, settlement, and production
remain in force.

The strict result also records
`serialized_facts_are_opaque_capability=false` and
`governed_policy_registry_join_verified=false`. These are required non-claims:
the JSON result is untrusted transport data, and the strict verifier does not
decide whether governance admitted its manifest, registry entry, or policy.

## Implemented Cycle-Free Config Upgrade

The restricted positive join requires the exact config schema:

```text
zenodex/zeno_ledger/replay_engine_config/v1
```

Its canonical document must add one `proof_authority_policy` object containing
the complete `GovernedProofAuthorityBindingV1`. The V1 config digest must hash
that object using a versioned `zeno_ledger_replay_engine_config_v1` domain. The
header's `config_digest` and the profile's accepted config-digest set then bind
the policy without adding an independent caller-selected policy input.

The governed policy ID deliberately excludes `profile_id`. Including it would
create a hash cycle:

```text
profile_id
  -> accepted config digest
  -> proof-authority policy ID
  -> profile_id
```

The final consumer still binds the selected profile independently through the
validated profile and its accepted config digest. The policy itself commits:

```text
chain ID
authority-manifest SHA-256
verifier-registry ID and entry ID
strict result schema
proof profile
validity interval
```

The V1 config parser rejects V0 documents with an injected policy field,
unknown policy keys, a noncanonical policy ID, or a policy whose recomputed ID
differs. V0 remains supported only as a non-authoritative diagnostic config.

The range verifier stable-reads one canonical strict payload, deterministically
replays the committed block, and supplies the exact pre-state and post-state to
the strict adapter. After the receipt is verified once, the adapter derives a
private compatibility proof that all four authenticated legacy Spot roots and
both ZenoLedger state-root-v5 values encode that same state pair. The accepted
profile is deliberately closed:

```text
one ledger height
one outer transaction
source-guest-validated operation-2 TauSwap arrays or operation-4 faucet framing
CPMM pools only
no vault, oracle, perps, or LP-duration-risk state
bounded canonical balance, pool, LP, fee, and nonce sections
```

The Spot and ZenoLedger root domains remain distinct. The bridge proves their
typed relation and never asserts byte equality.

This proof-authority profile does not reduce one outer transaction to one
economic action. Operation-4 faucet framing and multi-intent operation-2 arrays
remain inside the source guest's authenticated statement. Settlement promotion
requires a separately governed allowed-operation profile and canonical
per-action and nullifier semantics.

This is an implementation claim. The new range test uses a protocol-faithful
mock of the already reviewed strict process response; it does not regenerate a
fresh RISC0 receipt for the complete range path. The public proof-coverage
matrix therefore retains
`does_not_claim_proof_required_cryptographic_authority` until a final-source
real receipt is replayed through this exact join.

## Evidence

Focused tests cover:

- non-proof profiles returning an exact `not_required` decision;
- proof-required profiles returning the typed pending obligation;
- structural mode naming the missing replay-config digest;
- caller boolean mappings rejecting at the exact authenticated-result type;
- wrong committed policy rejection;
- not-yet-valid and stale policy rejection;
- policy-ID tampering rejection;
- private decision construction rejection;
- existing fabricated positive verification reports remaining rejected;
- cross-language state-root-v5 bridge vectors;
- authenticated source-root substitutions rejecting after one verifier call;
- duplicate-key strict payloads rejecting before verifier execution;
- multi-height V1 ranges rejecting before verifier execution;
- one successful singleton range invoking the governed verifier adapter once.

Replay commands:

```bash
python3 -m pytest -q \
  tests/integration/test_zeno_ledger_proof_authority_consumer_v1.py \
  tests/integration/test_zeno_ledger_proof_required_authority_wiring_v1.py \
  tests/integration/test_zeno_ledger_spot_state_domain_bridge_v1.py \
  tests/integration/test_zeno_ledger_strict_spot_authority_v1.py \
  tests/integration/test_zeno_ledger_strict_spot_range_authority_v1.py

python3 tools/check_zeno_ledger_proof_coverage_matrix.py --pretty
```

## Non-Claims

This lane does not claim:

- cryptographic proof authority for V0 profiles;
- multi-height or general application proof authority;
- general ledger/Spot state-domain equivalence outside the closed V1 profile;
- single-action settlement eligibility or production admission of faucet operations;
- hostile same-interpreter capability isolation;
- settlement authority;
- production authority;
- data availability or finality.
