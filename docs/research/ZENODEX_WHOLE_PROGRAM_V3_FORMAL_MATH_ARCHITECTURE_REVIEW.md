# V3 formal, mathematical, algorithm and architecture review

Date: 2026-09-05. Advisory review; authority `NONE`.

The committed review subject is
`7b2467067c8c978e9eca19ddd33a24ce0740560d`. The additional root and transfer-route
guests below are **uncommitted candidates**, separately identified by bytes.
This review changes no production code, theorem statement, policy, journal,
guest ABI or evidence pin. W04 projection/admission and the new history guard
were authored by this reviewer and are explicitly **self-review**. The scrutiny
of other proof statements, authentication, recursive guests and publication
architecture is independent of their implementation authors.

The evidence supports useful bounded accounting theorems and increasingly
concrete receipt verification. It does not establish formal completion of the
twelve lanes, whole-program runtime refinement or production value safety.
The severities below rank obstacles to those requested claims, not demonstrated
exploits. No publisher bypass was demonstrated in this review.

## Exact evidence and hard gates

The approved remote replay uses Lean `4.27.0`, Mathlib commit
`a3a10db0e9d66acbebf76c5e6a135066525ac900`, and CPU affinity limited to two CPUs.
The official Lean Linux release archive was checked against SHA-256
`0a62138ea5b9880a8eccd5e88d0920f93a58cf3428a9c78f99b8f4316383c69b`;
its Lean and Lake executables also matched the existing pinned local binary
hashes. Mathlib's existing dependency manifest matched
`6c24676b690a32627317b1d6dd58cf9318d689c5481e1edc53d07c93c892632f`.

Ten unchanged proof files compiled with `-DwarningAsError=true`. Placeholder
scanning found no placeholders or custom trust declarations in those files.
All 363 inventoried top-level theorem/lemma axiom probes passed with only
`propext`, `Quot.sound` and `Classical.choice` permitted. The count describes
the declarations replayed; it measures neither feature coverage nor theorem
importance. No theorem was newly constructed by this replay.

| Replay subject | Result | Receipt SHA-256 |
| --- | --- | --- |
| Eight core-only files: transfer V1 and challenge, structural global V1 and challenge, global V2, state refinement V2, its nonempty witness, and outcome V2 | 322 declarations; compile and axiom probes passed | `12ae2950a3367c3160b30e666b3de11c0a9749fff2579b690881065e94bfee4f` |
| Claimant/custody relation V1 and allocation-certificate model V1 | 41 declarations; compile and axiom probes passed | `c2e102121a5add2dab818307fa1bf71973fcf4a59d734b50094fbf63a2033985` |

The direct replay source manifest is
`7bdd9b06cb51b55eccc01c8c9f64dd85d4341505510d1cb9a1458a5fb1623615`;
its 67,633-byte archive is
`90cf082ffff34a23e91cff73f962c11f7243c14a1b742ef9098d48003a9e8385`.
Seven unchanged companion pytest gates were handed to the parent as an active
automatic job. Their 489,163-byte source archive is
`7a6ecbfef08facd5a3a3d9e31caefb7e910f93ba0ad731966bda381304575631`,
manifest `5433fecc65497c2151f47223cedff3eeabab58bd2e71363eef5bd96c4ed75f2b`.
Their final outcome must be read from `gates02-receipt.json` and its logs;
this review does not assume that outcome. The parent owns collection of the
remote compact evidence after the handoff.

Five existing companion source-pin checks passed locally. The history repair's
188 Python and 101 Rust checks are recorded in the separate allocation-binding
review. They are implementation regression evidence, not independent proofs
of the code authored by this reviewer.

## Severity-ranked findings

### FMA-01 — S1: a whole-state witness contract is not a transition-construction theorem

**CONFIRMED GAP.** `GlobalEconomicStateRefinementV2.lean:597` defines `Verified`
with both `ownedSupplyPre` and `ownedSupplyPost`, pre/post liability backing,
exact economic tables, lifecycle/replay checks and other conjuncts. At line 667,
`accepted_preserves_owned_supply` is exactly an extraction of
`accepted.verified.ownedSupplyPost`. At line 671, liability preservation likewise
extracts the postcondition. These are valid, useful checker-contract theorems.
They do not derive the postconditions by executing each intended command from
an invariant pre-state.

`GlobalEconomicStateRefinementV2Nonempty.lean:280`,
`combined_verified_relation_has_nonempty_asset_transfer`, constructs an actual
nonempty witness. This prevents the particular combined relation from being
entirely vacuous. It establishes one transfer example with abstract roots and
no external enqueue. It does not universally connect the implemented transition
function, its canonical decoding and all outcomes to `Verified`.

The gap is material to the whole-program target:

```text
authenticated initialization
and actual command execution
and implementation/formal simulation
must construct the combined witness;
then a trace induction can preserve the invariant.
```

The committed proof headers explicitly exclude that runtime refinement, so
this is a completion gap rather than a misleading theorem claim. Do not spend
the remaining GPU budget treating additional structural receipts as a repair
for this theorem gap. A useful next proof is a restricted, universally
quantified transfer-to-global-witness constructor followed by a trace theorem
that includes typed rejection and unchanged external effects.

### FMA-02 — S1: receipt cryptography does not qualify command authentication

**CONFIRMED GAP.** `economic_command_authentication_v1.py:84` authenticates an
intent through a bound command-signature backend; line 132 then binds the exact
intent to the sequenced occurrence, including subject, body, nonce, route and
validity interval. Those bindings are valuable and must remain.

However, `src/integration/economic_command_signature_verifier_deployment_v1.py:27`
still accepts a caller-supplied backend. Its module contract explicitly leaves
execution of the measured artifact by that backend as an external premise.
Searching `verify_command_signature` under `src` and `tools` found the protocol,
capability, authentication caller and measurement loader, without a concrete
backend for this economic-command interface. Other legacy signature systems
are not thereby qualified as implementations of this port.

The transfer guest executes a claimed context. Its Lean `Context`
(`AssetTransferRefinementV1.lean:239`) contains release and subject identifiers;
the authorization guard at line 330 compares sender with that subject. Neither
that equality nor a genuine module receipt proves that the subject signed the
economic intent. The current transfer-route guest preserves the subject/body/
grant bindings, but likewise takes this authentication premise from outside.

Next qualification needs a concrete measured signature backend with genuine
positive signatures and wrong signer/body/context/algorithm, malformed,
unavailable and after-replacement negatives. Preserve the existing two-stage
sign-then-sequence contract. Do not add arbitrary signature data to the proof
journal without first demonstrating that existing commitments are insufficient.

### FMA-03 — S1: exact allocation is not yet a publisher admission invariant

**CONFIRMED GAP; W04 portion is SELF-REVIEW.** At the committed subject,
`project_allocation_certificate_v1` has one integration consumer:
`global_allocation_shadow_v1.py:353`. The publisher's verified-to-commit path
(`global_economic_durable_publisher_v1.py:935` onward) does not call the
allocation projection or certificate checker. SHADOW's isolation is correct;
its agreement cannot serve as publication admission.

The uncommitted transfer-route guest calls the pure global allocation relation
at `shared/src/lib.rs:193`, then route projection and state/effect refinement.
It does not call the allocation producer or the certificate checker. The pure
relation establishes snapshot/occurrence binding and claimant continuity.
The state/effect refinement establishes backing inequalities. The certificate
separately requires the exact controlled-atom partition. Thus a route receipt
does not, on these calls alone, establish certificate acceptance.

This distinction is already represented by strong retained mathematics:
`GlobalClaimantCustodyRelationV1.overCollateralised_isBacked_notExact` at line 229,
`noUnclassified_premise_is_necessary` at line 263, and
`GlobalAccountingAllocationCertificateV1.certificate_implies_normativePartition`
at line 133. An authentic initialized exact partition plus a suitable
preservation theorem could discharge the missing implication for this narrow
transfer profile. It has not been demonstrated here. No reachable committed
counterexample or publisher bypass is claimed.

The history-root omission is repaired at this committed subject. Both runtime
refinements already required unchanged history, and the enclosing certificate
already bound the full state root. Do not restore that finding as an unresolved
publisher vulnerability, or equate module-local and coordinator state roots.

### FMA-04 — S1: twelve lane identifiers do not supply twelve lane lifecycles

**CONFIRMED GAP.** The producer registry at
`global_accounting_allocation_certificate_v1.py:109` has one receipt-backed
producer, nine `NO_PRODUCER` lanes, and two registered-empty lanes. The V3
requirements retain 103 capabilities and four cross-lane routes. Neither the
registry nor the formal lane enumeration supplies their command semantics.

| Lane | Current whole-allocation disposition | Required semantic closure still to establish |
| --- | --- | --- |
| ASSET_TRANSFER | One restricted producer | Account/asset lifecycle, registration, issue/burn, authentication and whole-state proof beyond a single transfer |
| SPOT_LIQUIDITY | No producer | Create/close, swaps, LP issue/burn, fees, rounding/residue ownership and terminal disposition |
| FARM_INCENTIVES | No producer | Stake/activation, emissions, claims, cancellation and terminal drain |
| ZDEX_TOKENOMICS | No producer | Fee-source ownership, staking/hosting/treasury claims, reserves, same-occurrence purchase/exact burn and retained supply |
| ZUSD_MONETARY | No producer | Collateral/debt ownership, monetary issuance/burn, redemption, stability pool, liquidation/recovery and final drain |
| PERPS_MARKET | No producer | Margin/funding/fee lifecycle, insurance, liquidation, ADL, bankruptcy and terminal closeout |
| ORACLE_MARKET | No producer | Query/tip/bond, authenticated finality, reward/dispute/clawback/slash and terminal drain |
| SEALED_AUCTION | No producer | Bond and inventory ownership, reveal/clear/settle, refund/slash, cancellation and expiry |
| STRATEGY_ESCROW | No producer | Reservation, activation/trigger/replacement, cancellation/expiry/recovery and Spot route authorization |
| PROOF_REWARDS | Registered empty, policy blocked | Funding ancestry, eligibility, nullifiers, payout and task terminal state |
| EXTERNAL_CUSTODY | Registered empty, disabled | Registered destinations, authentic finality, timeout/refund, delivery ancestry and destination idempotency |
| GOVERNANCE_MIGRATION | No producer | Constrained commands, profile/schema transitions, ownership continuity and exclusion of old writers |

This table does not assert that all component kernels are absent. Several
exist; their complete lifecycle-to-publication composition was not established
by the reviewed source or proofs. The four required routes remain separate:
fee-funded ZDEX purchase/burn, zUSD liquidation, perps epoch settlement and
strategy-triggered Spot. The new single-lane transfer route is not one of
those four cross-lane workflows. Disabled required features remain incomplete.

### FMA-05 — S2: recursive root proofs remain structural composition evidence

**CONFIRMED SCOPE LIMIT.** `global_economic_epoch_risc0/shared/src/preflight.rs:79`
checks ordered route claims, exact context, chained state roots and leaf counts.
The root guest verifies each prepared child claim and commits the prepared
journal. This proves exact execution of that checked composition. The epoch
preflight does not itself execute all lane commands or reconstruct all global
economic effects from full disclosed bodies. Those obligations belong to the
qualified route images and the enclosing runtime admission checks.

The root source06 evidence supplies an important improvement over the earlier
host-only controls: genuine raw guest execution without the required claim, or
with a wrong-journal claim, fails `sys_verify_integrity`. A genuine exact epoch
receipt is the positive control. The retained aggregate case exercises nine
commands through two same-image aggregation children. These close the named
absence of direct guest-negative and aggregate-branch evidence for that root
subject. They do not prove the economics of a journal-only structural child.

The root evidence archive read here is
`dc2843430247e087e9c0220e0cf3916c12b6d1bd41b9005786ea23ae189274d7`;
its guest-control artifact is
`dd28f99ccbda8a6fb6cfd95f38116c1ef1809fdbb2e1cf44a6df347fc644148d`.
This reviewer read the retained results and source, but did not independently
generate or cryptographically replay those receipts. The new transfer route's
real proof chain was still being built when its source was reviewed.

### FMA-06 — S2: finite-width and decoding refinement are not discharged by the current Lean abstractions

**CONFIRMED GAP.** The transfer model proves substantive arithmetic results:
`accepted_conserves_total` at line 738 derives conservation by summing the
aggregated role deltas; `accepted_deltas_i128` at line 766 and
`accepted_balances_u128` at line 808 establish mathematical bounds under explicit
guards and well-formed input premises. Fee-owner alias cases are included.

The runtime uses actual `u128`/`i128`, checked arithmetic, canonical ordered
tables and decoders. The Lean transfer model uses `Int`, a single-asset balance
function and a finite principal enumeration premise; the certificate model
uses `Nat` over three lanes, two domains and two claimants. The existing tests
bind source hashes and selected vectors, not a universally quantified decoder
or machine-integer simulation theorem. No `#[kani::proof]` or Kani harness was
found in the actual global ABI crate's source/tests.

Preserve the existing width guards and typed failures. Suitable next actual-Rust
obligations are the signed minimum magnitude in `checked_negative_sum`
(`asset_transfer.rs:57`), `apply_delta` at line 45, checked grouped folds
(`global_accounting_allocation_certificate.rs:596`), and bounded-vector decoding.
Use exact bounds and report unwind limits. A new Kani harness/toolchain requires
its own pinned source packet; it must not silently change the current guest ABI.

### FMA-07 — S1: production mediation, recovery and terminal effects remain open

**CONFIRMED GAP with deployment UNKNOWNs.** The new source-acquisition path is a
real architectural improvement: the exact writer capability is checked before
IO, one read transaction owns activation/source/tip/authority, the publisher
passes the store-derived state into the core, and commit rechecks CAS/authority.
The committed source-acquisition tests distinguish a historical retry source
from authority to publish a fresh stale transition.

It remains an isolated research publisher. The acquisition docstring at
`global_economic_epoch_journal_v1.py:790` explicitly retains verified creation,
publication and trusted process/store integrity as ancestry premises. Reopening
a structurally consistent file is not cryptographic reconstruction of those
premises. Original source-authorization roots are bound through an approved
profile manifest (`economic_initial_state_atom_coverage_v1.py:281,306`); the
coverage checker does not inspect hidden lane state or derive entitlement
authority from accounting totals.

Other value writers still exist, including the node's `_write_live_state`
(`tools/zeno_ledger_node.py:4176`), legacy Tau ingress and the DEX engine, plus
the separate M6 publication/delivery family. Which are mounted on an exact
deployment is **UNKNOWN** in this source-only review. No complete deployment
writer fence, atomic successor activation/old-writer retirement, concrete
datastore refinement or all-lane terminal delivery proof follows from these
tests. Logical rejection, committed retry and indeterminate acknowledgement
must retain their different outcome contracts.

## Proof quality beyond acceptance

The allocation partition theorem is a derived summation argument: it obtains
the lane partitions, rewrites aggregate/table equalities and uses natural-number
arithmetic. Its global conclusion is not stored as a field in `Tables`.
The transfer conservation proof likewise exposes the role-delta invariant.
These are reusable proof ideas, with bounded domains stated honestly.

The V2 combined witness is a useful architectural contract and a precise
inventory of obligations. Many public extraction lemmas are intentionally
definitional. Adding more such lemmas would not close FMA-01. The better next
proof constructs that record from an executable command and its authority
premises. The nonempty V2 example and the claimant-swap/domain-loss
counterexamples should remain required controls.

The heuristic proof-quality scanner found no placeholders/trust escapes in
the three selected files. Its broad-automation warnings concentrate in
`AssetTransferRefinementV1.roleOrdered_eq_intended:852`, whose three branches
correspond to real fee-owner alias cases. That is not by itself unjustified
enumeration. Its code-style scores are not used as formal-completeness grades.

## Ranked algorithm and proof-improvement candidates

These are proposals, not implementations or measured speedup claims.

1. **Construct the restricted transfer preservation bridge.** Inputs: one
   authenticated occurrence, exact complete predecessor, governed module
   transition and coordinator projection. Output: the combined state/effect
   witness and an exact allocation-preservation implication. Preserve all
   claimant identities, custody, history, replay uniqueness and finite-width
   guards. First use the existing transfer transition and 37 relation cases as
   the baseline. Require a quantified theorem, a valid nonzero-history witness,
   authority/conserved-claimant negatives and an omission mutant. This has
   higher assurance payoff than adding more root-positive examples.

2. **Replace whole-table map rebuilding with a verified sparse merge.** The
   transfer affects at most three principal roles after alias aggregation.
   Python `_post_balances:102` rebuilds and sorts the table; Rust
   `post_balances:72` reconstructs a `BTreeMap`. Target a canonical linear merge
   of the sorted old table with the at-most-three aggregated deltas:
   `O(N + k log k)` work, `k <= 3`, versus rebuilding/sorting at `O(N log N)`.
   The output still needs `O(N)` storage and hashing. Prove exact rows, zero
   elision, untouched assets, alias handling and rejection precedence. In
   particular, a lexically early credit overflow cannot outrank a debit failure.
   Benchmark 0/1/maximum-neighbor/4096 rows and all alias classes, reporting
   canonical bytes, allocations, cycles and exact failures. Keep the current
   implementation as differential oracle until a verified successor passes.

3. **Bound publication validation cost without weakening ancestry.** Every
   source acquisition and commit calls `_validate_store_v1:1047`, which performs
   schema integrity checking and decodes the full history. The current ceiling
   is 4096 epochs and 512 MiB (`global_economic_epoch_journal_v1.py:46`). For
   `H` similarly sized epochs of size `B`, repeated full validation creates
   `O(HB)` work per append and `O(H²B)` cumulative work. This is static complexity
   analysis; no latency benchmark was run. First benchmark histories of
   1/8/64/512/4096 on isolated infrastructure. A candidate authenticated checkpoint
   plus exact suffix validation must preserve predecessor completeness, current
   authority, exact retry, rollback detection and invalidation on store changes.
   Reuse already committed identities where sufficient. Do not add a redundant
   journal commitment or trust a bare cached head merely to obtain speed.

4. **Generalize the allocation sum theorem before adding lane assignment search.**
   Replace the three-lane/two-claimant summation model with finite indexed maps
   and prove that exact per-lane partitions aggregate to the global partition.
   Separately prove the checked-`u128` fold simulation, including overflow
   refusal and group order. Preserve the direct small model as an independent
   oracle. Missing ownership information remains a policy/provenance gap:
   a deterministic or unique feasible assignment does not make it authorized.
   The existing `terminalProjection_hasNoUniversalDomainRecovery:613` is a
   load-bearing impossibility result, not a prompt to guess a domain.

5. **Choose recursive grouping by measured proof cost while retaining exact order.**
   Current bounds are 1–8 direct route assumptions and 1–64 commands. After the
   genuine economic route chain works, compare fixed contiguous groups against
   a deterministic dynamic program over at most 64 commands minimizing measured
   proving cost subject to journal-byte and child-count bounds. The invariant is
   identical ordered occurrences, context, boundary roots and exact child claims;
   changing grouping cannot reorder or discard commands. Use exhaustive grouping
   enumeration for small `n`, and compare framed bytes, cycles, memory and proof
   verification time. No throughput or cost improvement is presently claimed.

## Runpod priorities and remaining unknowns

Run the seven unchanged Lean companion gates already submitted, then the three
existing ESSO gates for claimant/custody, allocation certificate and structural
global core with their pinned solvers and meaningful mutants. The global-core
gate records ESSO code hash `7f80c6216be85c827e8d1cc2fa08ee3107a74588`.
Preserve its bounded and abstract-authority premises. Next prefer the genuine
module/coordinator/economic-route/root chain and direct guest negative controls.
Actual-Rust bounded arithmetic/parser proofs and the constructive transfer
bridge are separate targeted work packets, not consequences of more receipts.

This review did not replay all ESSO, Kani, Tau, twelve-lane, four-route or mounted
deployment gates. It did not validate external finality, sovereign policy
choices, signer infrastructure, production writer inventory, terminal delivery,
all resource ceilings or all crash interleavings. Those are `UNKNOWN` or the
explicit confirmed gaps above. No capability-completion percentage or blanket
review grade is warranted.

## Uncommitted candidate identities and reproducibility

The candidate inventory contained 37 files under the root guest, transfer-route
guest and shared receipt endpoint. Its temporary manifest SHA-256 was
`a08604101cbcb3341624658189a7dc058347275dad91912a6609115973b606a0`.
The following are the code subjects relied on by this review; subsequent edits
require a successor review rather than treating these results as current.

| Candidate path | SHA-256 |
| --- | --- |
| `zk/global_economic_root_risc0/shared/src/lib.rs` | `44e75a89c14f5de636ee409ac077fe8a3b030ff1cc16f64f2231cddf89ea4f5c` |
| `zk/global_economic_root_risc0/methods/root/src/main.rs` | `26232395e8766451228bad1e9828392d043da59502f16cfdf33447fcfce56d15` |
| `zk/global_economic_root_risc0/host/src/lib.rs` | `5efc3723d344339a0f8575f8ece9b71c42389ec110c86841ffdcbc3df20e395f` |
| `zk/asset_transfer_route_composer_risc0/shared/src/lib.rs` | `1f54a595e85f4dafec8202f774191892ce1868a0eb98cfb7b4d5fce0aa13ad14` |
| `zk/asset_transfer_route_composer_risc0/methods/guest/src/main.rs` | `f8f169563575dc847150d4041bc4ab89ceebcd2888bb79d11883da195ac4fbfd` |
| `zk/asset_transfer_route_composer_risc0/host/src/lib.rs` | `bc740bde93867368a095bc1c379370fa64715ebacaa1729352731e77385f1ea2` |
| `zk/risc0_receipt_verifier_v1/mod.rs` | `5a638c33944186c798233fd2bffb919ee9ae9558d13512186e952b44edada050` |
| `zk/risc0_receipt_verifier_v1/protocol.rs` | `d626fc7cc969f42504d9ff19d59570071fd049a6b1fed6e0b6cc2101d8060b82` |

The dirty measured-verifier-set patch and exporter additions were inventoried
but not promoted into the committed subject or independently qualified here.
The earlier source04 root review remains a historical exact-source review;
the source06 controls supply the specifically described later evidence.
At the final drift check, the eight code hashes above still matched. The
uncommitted `host/tests/real_aggregation.rs` under the root guest had changed,
and a new dirty coordinator shared-source change appeared with SHA-256
`6fa26f516de55093aa66c7234d3a10c3d7b91c9b7f7374c3cc870ae780860850`.
Those later changes are unreviewed successors, not part of this verdict.

Commands performed included exact `git rev-parse HEAD`/`git status --short`,
bounded `rg` caller/producer/writer/Kani inventories, line-numbered source and
theorem reads, SHA-256 comparisons, the repository placeholder scanner, and:

```bash
python3 ~/.codex/skills/proof-quality-curation/scripts/lean_proof_quality_scan.py \
  lean-mathlib/Proofs/GlobalEconomicStateRefinementV2.lean \
  lean-mathlib/Proofs/GlobalAccountingAllocationCertificateV1.lean \
  lean-mathlib/Proofs/AssetTransferRefinementV1.lean
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider \
  tests/formal/test_lean_global_accounting_allocation_certificate_v1.py \
  tests/formal/test_lean_global_claimant_custody_relation_v1.py \
  tests/formal/test_lean_global_settlement_core_v2.py \
  tests/formal/test_lean_global_economic_state_nonempty_v2.py \
  tests/formal/test_lean_global_economic_refinement_outcome_v2.py \
  -k 'sources_are_pinned or sources_are_exactly_pinned'
```

The source-pin selection passed five tests with 46 deselected and ran no local
Lean build. The remote direct replay command was the source-hashed
`run_replay.py LEAN A NEW_OUTPUT` or `run_replay.py LEAN B NEW_OUTPUT
--dependency-path PINNED_MATHLIB_PATH`; its receipt retains every exact compiler
argument, output hash and timeout result.
