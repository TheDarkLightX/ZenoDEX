# ZenoLedger Spot Proof Authority Boundary V1

Status: scoped verifier result and restricted singleton ledger-authority join
implemented; settlement and production authority remain disabled.

## Purpose

The state-proof CLI has two distinct Spot verification surfaces:

- `tau_state_proof_verify` preserves the existing diagnostic behavior and its
  optional outer checks.
- `zenodex.zeno_ledger.risc0_spot_authority_verify.v1` requires an exact block,
  Tau state, Spot context, ZenoLedger header, replay config, and governed
  authority-expectation object.

The strict surface verifies the RISC0 receipt exactly once under the compiled
generic Spot guest image. It then consumes the private verified-receipt value to
check the authenticated journal and every outer binding that the current V1
journal can support.

```text
strict canonical request
  -> exact request and expectation schemas
  -> one image-bound RISC0 receipt verification
  -> authenticated StateProofJournalV1
  -> block/Tau/context recomposition
  -> transaction-domain bridge
  -> exact outer expectation bindings
  -> scoped authenticated Spot facts
```

Caller-provided `ok`, `verified`, `production_authority`, or similar Boolean
fields are rejected as unknown fields. They cannot create the private verified
receipt value or appear in the exact authority-expectation schema.

## Governed join fields

The result schema is exactly:

```text
zenodex.zeno_ledger.authenticated_spot_proof_facts.v1
```

The result carries the identities needed by a separate governed ledger
consumer:

```text
authority_manifest_sha256
verifier_registry_id
verifier_registry_entry_id
policy_id
chain_id
height
valid_from_height
valid_until_height
proof_profile
canonical_header_hash
proof_metadata_hash
proof_commitment
config_digest
```

`policy_id` is a canonical lowercase 32-byte `0x` root. It is not a free-form
policy label.

The CLI checks the supplied expectation object for exact shape and internal
consistency. Governance remains responsible for selecting the expected
manifest, registry entry, and policy. The ledger consumer must compare these
returned identities to governed state before admitting them.

`proof_commitment` is recomputed from the exact proof envelope using the
ZenoLedger `risc0_tau_state_proof_envelope_v0` domain. The expected proof
metadata hash must equal the header's `proof_journal_hash`. The strict CLI does
not receive or validate the complete metadata object, so
`proof_metadata_object_verified` remains false; the ledger consumer owns that
separate exact-object check.

The enclosing block timestamp and context timestamp must agree. The header's
millisecond timestamp must fall within that same integer second. This closes
the temporal join without claiming that the current Spot journal directly
commits the timestamp.

## Replay-config V1 authority binding

The strict schema requires:

```text
zenodex/zeno_ledger/replay_engine_config/v1
bounded_dex_engine_proof_authority_v1
```

Its top-level keys are exactly `schema`, `profile`, `config`, and
`proof_authority_policy`. The engine projection is the same exact canonical
bounded projection accepted by the Python V1 parser. Reduced projections,
unknown keys, changed fixed limits, floats, and V0 documents reject.

The proof-authority policy has the exact schema
`zenodex.zeno_ledger.governed_proof_authority_binding.v1`. It commits the chain,
authority-manifest SHA-256, verifier-registry and entry roots, strict result
schema, proof profile, and finite height interval. Rust independently derives:

```text
policy_id = hash_v0(
  governed_proof_authority_binding_v1,
  exact policy object without policy_id
)

config_digest = hash_v0(
  zeno_ledger_replay_engine_config_v1,
  complete exact V1 config document
)
```

Every recomputed policy field must equal the strict expectation, and the V1
config digest must equal both the expectation and header. The Python/Rust
parity vectors are:

```text
policy_id    = 0xa33a534c7c1b17e49e8710a904849ec0db74e150ab579cf37c0b434447606825
config_digest = 0x5f5869a1291ea7b17b57bb07d1394ad9ba880f202725755b8995226c3938415f
```

The ordinary diagnostic verifier retains its existing V0-compatible behavior.
V0 is inadmissible on the strict authority schema.

## Transaction domain bridge

The strict verifier derives both commitments from the same ordered JSON
transaction array:

```text
same canonical transaction bytes
  -> parsed TauTxV1 sequence -> Spot txs_commitment_v1
  -> ZenoLedger tx_hash_v0 leaves -> ZenoLedger tx_root_v0
```

The commitments have different encodings and domain separators. The result
therefore returns both values and states `roots_are_domain_distinct=true`.
Equality between these roots is neither expected nor accepted as a bridge.

The transaction bridge rejects unknown transaction, operation, intent, route,
and faucet fields before either commitment is derived. A transaction-local
timestamp, when present, must equal the enclosing block timestamp. The V1
bridge also rejects non-ASCII strings and object keys. This deliberately narrow
surface keeps the Rust and Python canonical-byte domains aligned while a future
shared typed transaction codec is developed. Empty, one-leaf, and odd
three-leaf Python parity vectors pin the ZenoLedger Merkle behavior.

## Exact non-claims

The current `StateProofJournalV1` does not directly commit:

- ZenoLedger chain ID or height;
- the block timestamp as a public journal field;
- the ZenoLedger replay-config digest;
- the ZenoLedger pre-state or post-state root domains;
- data-availability verification evidence.

The strict outer verifier binds those contextual identities to its scoped
result, while keeping these result flags false:

```text
block_timestamp_directly_committed_in_spot_journal
chain_and_height_directly_committed_in_spot_journal
spot_app_hash_equals_zeno_ledger_state_root_verified
data_availability_verified
proof_metadata_object_verified
serialized_facts_are_opaque_capability
governed_policy_registry_join_verified
settlement_authority
production_authority
```

In particular, the authenticated Spot `pre_app_hash` and `post_app_hash` are
returned alongside the header's ZenoLedger state roots. The implementation does
not relabel one root domain as the other.

A restricted outer bridge can now join those domain-distinct roots after exact
ledger replay. It independently derives the legacy Spot application and nonce
roots and the ZenoLedger state-root-v5 pair from the same pre-state/post-state
objects. This leaves
`spot_app_hash_equals_zeno_ledger_state_root_verified=false`, because equality
is still false, while proving a stronger typed compatibility relation for the
closed singleton profile.

The serialized result is untrusted data after it crosses the process boundary.
It is not the private verified-receipt value and cannot serve as an opaque
authentication capability. A pinned consumer adapter must execute the governed
verifier, validate the exact result schema, and join every returned governance
identity to its own governed state. This V1 CLI therefore reports
`serialized_facts_are_opaque_capability=false` and
`governed_policy_registry_join_verified=false`.

## Remaining promotion work

The governed consumer and replay-bound singleton range path are now connected.
The range path accepts only canonical config V1, an exact governed policy,
stable-read strict payload bytes, one exact replayed state pair, and one private
strict-verifier observation carrying the restricted bridge capability. A
multi-height range rejects until a typed range-level authority capability is
defined.

The connection is covered by deterministic protocol tests. Fresh
final-source receipt replay through the complete range path remains a separate
promotion requirement, so the public proof-coverage matrix is unchanged.

The operational CLI now reaches this singleton governed path only when all
four authority inputs are supplied together:

```text
--strict-spot-request-payloads-dir <canonical payload directory>
--strict-spot-verifier-executable <absolute static verifier path>
--strict-spot-authority-manifest <canonical manifest file>
--verifier-registry <canonical registry file>
```

The loader performs stable bounded reads, rejects duplicate keys, floats,
noncanonical bytes, and JSON nesting beyond 64 levels, and recomputes the
manifest SHA-256. Replay-config V1 must commit that exact digest and the exact
registry identities before the verifier can execute. Partial argument groups
reject during CLI parsing. This operational reachability does not satisfy
final-source release evidence, external checkpoint finality, settlement
authority, or production authority.

Settlement promotion still requires an exact guest-committed settlement-effect
plan, typed cell-transition openings, data-availability and finality gates, and
one atomic application-state commit. The current bridge excludes vault, oracle,
perps, LP-duration-risk, non-CPMM, and multi-transaction state. It therefore
closes one narrow proof-authority path without closing the settlement or
production gap.

The source guest's current transaction surface can still contain multiple
operation-2 TauSwap intents or operation-4 faucet framing. Proof authority
authenticates that governed source statement; it does not make those operations
settlement-eligible. A later allowed-operation profile and canonical
per-action/nullifier proof are mandatory before economic authority is enabled.
