# FCIS Support Root Profile v5

Status: normative specification for an unmounted M5 prerequisite

Profile ID: `zenodex/fcis/support-profile/v5`

Profile version: `5`

Implementation:
`src/core/fcis_support_profile_v5.py`

Constants:
`src/core/fcis_support_profile_constants_v5.py`

Golden vectors:
`docs/specs/fcis_support_root_v5_golden_vectors.json`

Generator:
`tools/generate_fcis_support_root_v5_vectors.py`

## 1. Scope and authority

The v5 support root commits the exact pre-state cells and execution context
that can affect one admitted FCIS spot-step evaluation. It is evidence attached
to the evaluator result. It is not a post-state root, an authorization witness,
or a substitute for the full committed-state root.

```text
support_root_v5
  = H(project(exact_pre_state, declared_support(command, context)))
```

The declaration and observation paths are independent:

```text
OwnedCommand + ExactContext + ExactPreStatePoolMetadata
  -> DeclaredSupportV5

ExactSequentialEvaluation + TypedReadCombinators
  -> ObservedReadTraceV5

ObservedReadTraceV5 subset DeclaredSupportV5
  -> support-root evidence may be constructed
```

The observed trace must never be populated from the declared support. An
undeclared read rejects evidence construction. No partial evidence is returned.

Mounted support-root v4 bytes, vectors, and meaning remain frozen. Profile v5
stays unmounted until Python/Rust parity, proof-consumer migration, and the
remaining M5 promotion gates pass.

The earlier `compute_support_state_root_for_batch_owned_committed_v1` and
`compute_support_state_root_v5_with_committed_spot_state_v1` prototype bytes
remain available only as frozen differential fixtures. They omit the complete
command, context, presence, fee, recipient, and read-containment contract and
do not implement this profile. Version number `5` alone is therefore never
sufficient authority. Every completed-v5 receipt must also bind profile ID
`zenodex/fcis/support-profile/v5`.

## 2. Admitted inputs

The root function accepts only these exact owned values:

1. `OwnedSettlementV1`;
2. `tuple[OwnedIntentV1, ...]` in protocol order;
3. `FCISStepExecutionContextV1`;
4. `CommittedBalanceTableV1`;
5. `OwnedMapV1[str, CommittedPoolStateV1]`;
6. `CommittedLPTableV1`;
7. `CommittedNonceTableV1`;
8. `CommittedFeeAccumulatorStateV1`;
9. `FCISStateReadTraceV5`;
10. `FCISContextReadTraceV5`.

The public function re-admits every authority-bearing value through its closed
profile. The evaluator-owned private sink receives the single already-admitted
graph and performs no second admission.

Vault, Oracle, and perps state are outside this local spot support projection.
They remain bound by the full pre-state root. A command profile that consults
one of those fields must introduce a new support-profile version before it can
mount.

## 3. Closed coverage inventory

The source inventory is generated from `IntentKind`,
`intent_allowed_field_names_v1`, and the execution-context schemas. A new
intent kind or context field causes an import-time or executable inventory
failure until the support dependency is declared.

The following table is normative. “Cell” includes presence or absence and, when
present, the complete value described in section 6.

| Intent kind | Declared pre-state cells |
| --- | --- |
| `create_pool` | sender balances for `asset0` and `asset1`; derived pool ID cell; creator and locked LP cells for that pool; sender nonce |
| `add_liquidity` | pool ID cell; sender balances for both pool assets when the pool or an earlier create command supplies those assets; recipient LP aggregate cell; sender nonce |
| `remove_liquidity` | pool ID cell; recipient balances for both pool assets when known; sender LP aggregate cell; sender nonce |
| `swap_exact_in` | sender `asset_in` balance; actual recipient `asset_out` balance; pool ID cell; sender nonce; active protocol-fee recipient `asset_in` balance when its share is nonzero |
| `swap_exact_out` | same support classes as `swap_exact_in` |
| `route_exact_in` | sender `asset_in` balance; actual recipient `asset_out` balance; every route-leg and fingerprint pool cell; sender nonce; active protocol-fee recipient `asset_in` balance when its share is nonzero |
| `route_exact_out` | same support classes as `route_exact_in` |

If `fee_split_policy` is present, the fee-accumulator cell is included. Every
context schema path is conservatively included because it may affect
admission, rejection, arithmetic, effects, receipts, or policy selection.

The complete command is separately bound by the command root. Support
dependencies do not replace command encoding. Every source-allowed intent field
has exactly one explicit classification: support dependency or command-only.
The two classes are duplicate-free, disjoint, and their union must equal the
source-derived allowed-field inventory for each intent kind. A new field or
intent kind therefore fails import and tests until it is classified.

## 4. Typed deterministic read combinators

Semantic reads in the sequential reference must use the closed read
operations in `src/core/fcis_traced_reads_v5.py` and the observed leaf
transitions they call:

```text
read_step_execution_context_v5
read_balance_v5
read_pool_v5
read_nonce_v5
read_fee_accumulator_v5
route_binding_pins_snapshot_traced_v5
replay_route_legs_traced_v5
apply_spot_deltas_traced_v5
```

Each combinator is a total pure function over exact values:

```text
(ExactState, Trace, ExactKeyOrInput)
  -> (ValueOrTypedTransitionResult, ExtendedTrace)
```

Balance, pool, LP, route-pin, and route-replay leaf operations emit keys at
their semantic lookup sites. The aggregate spot operation returns its result
and canonical read set on every success and rejection path. Its traced wrapper
extends the caller trace only from that leaf-produced read set. It never infers
reads from deltas, patches, bindings, or declared support. Pool-patch
composition touches only the two input patches and does not scan unrelated
pool cells.

The context operation uses the explicit
`FCIS_CONTEXT_PROJECTION_PATHS_V5` classification. Import fails unless that
classification exactly equals the source-derived closed context schema. The
operation explicitly projects every classified scalar, policy presence cell,
and present nested policy field, then returns the corresponding conservative
context trace. The structural checker derives required attribute accesses from
the explicit classification.

Each state combinator performs exactly one declared semantic operation, returns
a new canonical trace, and cannot access the declared support set. Direct state
reads on the exact evaluator path are structural-checker violations.

Representation revalidation at the public boundary is not a semantic state
read. It reconstructs the exact owned graph before evaluation and does not
replace trace instrumentation.

## 5. Canonical primitives

All integer lengths and nonnegative values use minimal unsigned LEB128
(`encode_uvarint`) with a 256-bit upper bound.

```text
bytes(x) = uvarint(len(x)) || x

domain(label, version)
  = ASCII("zenodex:" || label || ":v" || decimal(version)) || 0x00

H(x) = "0x" || lowercase_hex(SHA-256(x))
```

Public keys are exactly 48 decoded bytes. Asset and pool identifiers are
exactly 32 decoded bytes. The closed admission profiles establish canonical
lowercase `0x` spellings before the identifiers reach this encoder.

Every tuple in a support set and read trace is lexicographically sorted,
duplicate-free, and exact-typed.

## 6. Presence and value encodings

Omission never proves non-membership. Each declared key appears in canonical
order and carries an explicit presence encoding.

### 6.1 Balance cell

```text
balance_cell =
    pubkey[48]
 || asset[32]
 || present:uvarint
 || (amount:uvarint if present = 1)
```

Absent is tag `0`. Present is tag `1`. Committed balances are sparse, so zero
has the semantic absent representation.

### 6.2 Pool cell

```text
pool_cell =
    pool_id[32]
 || present:uvarint
 || (canonical_pool_body_v1 if present = 1)
```

Pool bodies use `_encode_pool_body_v1` from the committed spot-root codec. A
pool identifier and its complete pool body must agree under exact-state
admission.

### 6.3 LP aggregate cell

Each `(pubkey, pool_id)` key commits five optional components in this order:

1. LP balance;
2. last mint timestamp;
3. last remove timestamp;
4. churn tier;
5. last churn-update timestamp.

```text
optional_int(None)    = uvarint(0)
optional_int(Some(x)) = uvarint(1) || uvarint(x)
```

The key bytes precede the five component encodings. This distinguishes absent
metadata from present zero.

### 6.4 Nonce cell

```text
nonce_cell =
    pubkey[48]
 || optional_int(nonce)
```

Absent and present zero have distinct preimages.

### 6.5 Fee accumulator

```text
fee_cell = uvarint(0)
         | uvarint(1) || uvarint(dust)
```

Tag `0` means the support profile excludes the accumulator. Tag `1` means it is
included and commits the exact dust value.

## 7. Support-set preimage

Let:

```text
pair_keys(keys, left_width, right_width)
  = uvarint(count)
 || concat(fixed(left, left_width) || fixed(right, right_width))

string_keys(keys, width)
  = uvarint(count)
 || concat(fixed(key, width))
```

The support-set preimage is:

```text
domain("fcis_support_set", 5)
|| "BAL" || bytes(pair_keys(balance_keys, 48, 32))
|| "POL" || bytes(string_keys(pool_ids, 32))
|| "LPK" || bytes(pair_keys(lp_keys, 48, 32))
|| "NNC" || bytes(string_keys(nonce_keys, 48))
|| "FEE" || bytes(uvarint(include_fee_accumulator ? 1 : 0))
|| "CTX" || bytes(
     uvarint(context_path_count)
     || concat(bytes(UTF8(context_path)))
   )
```

```text
support_set_commitment = H(support_set_preimage)
```

## 8. Command and context commitments

The command-root preimage is:

```text
domain("fcis_support_command", 5)
|| "SET" || bytes(canonical_owned_settlement_bytes_v1)
|| "INT" || uvarint(intent_count)
|| concat(bytes(canonical_owned_intent_bytes_v1(intent_i)))
```

Intent order is the admitted protocol order and is not re-sorted.

The execution-context hash is:

```text
H(
  domain("fcis_step_execution_context", 1)
  || encode_fcis_execution_context_v1(
       "zenodex/fcis/context/step-value/v1",
       exact_context
     )
)
```

## 9. Root preimage

Each section is `label[3] || bytes(section)`, in this exact order:

```text
domain("state_support_root", 5)
|| "CMD" || bytes(command_root[32])
|| "CTX" || bytes(execution_context_hash[32])
|| "SUP" || bytes(support_set_commitment[32])
|| "BAL" || bytes(balance_presence_section)
|| "POL" || bytes(pool_presence_section)
|| "LPS" || bytes(lp_presence_section)
|| "NNC" || bytes(nonce_presence_section)
|| "FEE" || bytes(fee_presence_section)
```

```text
support_root_v5 = H(root_preimage)
```

## 10. Required laws

For every admitted profile input:

```text
Totality:
  evaluation returns one typed result or one typed rejection;
  no host exception crosses the mounted boundary.

Determinism:
  equal exact inputs produce byte-identical evidence.

Pre-state binding:
  evidence projects the exact pre-state, never the successor.

Containment:
  ActualStateReads subset DeclaredSupportState
  ActualContextReads subset DeclaredSupportContext

Irrelevance:
  states equal on declared support produce equal support roots.

Sensitivity:
  changing a declared key, presence tag, or committed value changes the
  relevant preimage and, absent a SHA-256 collision, the root.

Canonicality:
  support keys and traces are sorted and duplicate-free;
  complete-input encoders have one accepted byte spelling.

Version separation:
  v4 bytes and semantics remain unchanged.
```

The executable evidence includes example, boundary, mutation-killing, and
deterministic Hypothesis tests. The structural checker rejects direct reads,
trace/support coupling, post-state substitution, omitted context paths,
whole-map patch scans, read evidence inferred from intended writes, rejection
paths that discard reads, and missing containment.

## 11. Resource bounds

This profile inherits exact admission limits for input bytes, graph depth,
nodes, collection sizes, identifier widths, and integer magnitude. M5
promotion also requires the reviewed `TransitionBudgetV1` to bind maximum
reads, writes, effects, outbox records, witness bytes, and receipt bytes.

The golden-vector generator is deterministic and performs no network, clock,
randomness, locale, or environment reads. Its document binds stable algorithm,
schema, generator, and canonical-codec identifiers; hashes every direct source
dependency and its complete repository-local transitive import closure; hashes
the structural checker and locked toolchain inputs; and hashes the canonical
source manifest.

## 12. Promotion state and nonclaims

Current status:

```text
Python v5 encoder and evidence: implemented, unmounted
Sequential typed read trace: implemented, unmounted
Python golden vectors: required in this P1 checkpoint
Rust byte parity: open
Proof-guest binding: open
Tau adapter binding: open where supported
Production authority switch: forbidden
Datastore linearizability: not claimed
Crash-safe external delivery: not claimed
```

Failure of any required parity or migration lane keeps the exact evaluator in
shadow-only status and yields `M5_BLOCKED_NO_AUTHORITY_SWITCH`.
