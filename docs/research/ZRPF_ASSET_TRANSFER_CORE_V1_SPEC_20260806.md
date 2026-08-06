# ZRPF Asset Transfer Core V1

Status: implemented and tested ordinary-transfer functional core; research-only,
SHADOW, unmounted, and without guest-receipt, settlement, publication, or
production authority.

Date: 2026-08-06

## Purpose

The whole-economy ABI already defines the `ASSET_TRANSFER` lane, canonical
account-movement effects, governed module releases, route selection, and a
proof-neutral lane journal. It previously lacked a deterministic lane function
that derives an ordinary transfer from bounded typed state.

Asset Transfer Core V1 closes that arithmetic and typed-transition gap for one
command shape:

```text
transfer(source, destination, asset, amount_atoms)
```

Managed issuance, burn, transaction fees, nonce consumption, migration, and
terminal account lifecycle remain outside this slice.

## ShapeForge model

The repository's promoted ShapeForge seed informed this bounded Phi and the
explicit gap record. No incomplete ShapeForge artifact was treated as evidence.

```text
Phi := <
  M = asset_transfer_core_v1,
  S = one_ordinary_same_ledger_account_transfer,
  A = representation_and_refinement_binding,
  T = shared_no_std_arithmetic_plus_typed_leaf_boundary,
  V = canonical_balances, source, destination, asset, amount,
      expected_pre_root, expected_command_hash, expected_subject,
      post_balances, account_movement, conservation_totals, receipt_hash,
  O = construct, canonicalize, hash, authorize_shape, debit_credit,
      conserve, project_global_movement, exact_encode,
  G = nonzero_identifiers, integer_atoms, one_to_2^112_minus_1,
      zero_to_256_cells, unique_sorted_keys, checked_arithmetic,
      insufficient_precedes_overflow, reject_has_no_candidate_post_state,
  Obs = accepted_derived_transition_or_stable_typed_reject,
  K = state_root_plus_command_hash_plus_leaf_receipt_hash,
  E = failure_first_compile, AAA, BVA, bounded_exhaustive_oracle,
      metamorphic_permutation, codec_mutation, runtime_regression,
      source_closure,
  Gap = authenticated_occurrence, grant_and_nonce, validity_epoch,
        complete_lane_openings, global_post_root, effect_reconciliation,
        module_release, route, RISC0_3_0_6_guest, real_receipt,
        release_aware_verifier, atomic_publisher,
  N = zero_or_excess_amount, self_transfer, duplicate_cell, excess_capacity,
      insufficient_funds, recipient_overflow, wrong_root, wrong_command,
      wrong_subject, malformed_or_noncanonical_input,
  Delta = runtime_and_future_guest_share_one_transfer_arithmetic_function
>
```

Strongest evidence class: `tested implementation`.

## Correct-by-construction boundary

The arithmetic crate is `no_std`, dependency-free, deterministic, and imported
by both the established Rust runtime balance kernel and the ZRPF protocol
transition:

```text
settle_transfer_balances_v1(source_pre, destination_pre, amount)
  -> post balances
   | InsufficientBalance
   | BalanceOverflow
```

The function checks insufficient source funds before recipient overflow and
uses checked addition. Its admitted balance and amount range is
`1..=2^112-1`. The runtime wrapper retains its existing public API and rejection
codes while delegating this arithmetic to the shared crate.

The typed leaf function is:

```text
execute_asset_transfer_leaf_v1(input)
  -> Accepted(post_state, movement, totals, receipt_hash)
   | Rejected(stable_code)
   | internal_contract_error
```

An accepted transition reconstructs canonical state, projects exactly one
`GlobalEconomicEffectKindV1::AccountMovement` row for `ASSET_TRANSFER`, and
checks exact per-asset conservation. A rejected variant cannot contain a
candidate post-state, movement, or effect plan.

## Canonical state and commitments

State contains at most 256 positive balance cells. Keys are exact
`(account_id, asset_id)` pairs, sorted lexicographically and unique. Zero cells
are absent. Construction canonicalizes input order; decoding requires canonical
order and recomputes the committed state root.

State roots, command hashes, and leaf receipt hashes use distinct SHA-256
domains and length-delimited fields. The leaf receipt binds the expected
pre-state root, expected command hash, expected authorization subject, command,
derived post-state root, movement, and pre/post conservation totals. Exact
Postcard decoding rejects empty, oversized, trailing, malformed,
self-inconsistent, or noncanonical input.

## Stable rejects

| Code | Meaning |
|---:|---|
| 1001 | expected pre-state root differs from the supplied canonical state |
| 1002 | expected command hash differs from the supplied canonical command |
| 1003 | expected authorization subject differs from the source account |
| 1004 | source balance is insufficient |
| 1005 | recipient balance would exceed `2^112-1` |
| 1006 | an accepted transfer would exceed 256 stored cells |

These convert to nonzero `LaneModuleRejectCodeV1` values. The current leaf
outcome is proof-neutral and does not construct a lane journal.

## Executable evidence

Tests follow Arrange, Act, Assert flow and cover:

- command boundaries at zero, one atom, maximum, and maximum plus one;
- exact-balance sparse removal, insufficient funds, recipient maximum plus
  one, maximum transfer, and full-state capacity;
- state cardinality at 256 and 257, duplicate cells, zero balances, and
  oversized balances;
- distinct pre-root, command-hash, and subject mismatch rejects;
- a bounded independent oracle over source and destination balances `0..=8`
  and amounts `1..=9`;
- conservation and preservation of unrelated accounts and assets;
- identical roots and outcomes under input permutation;
- exact bounded codec behavior and nested version or unknown-field mutation;
- semantic-field binding in command and receipt hashes;
- all stable reject-code conversions;
- the existing runtime balance-kernel regression suite after shared-core
  extraction;
- exact governed source inventory closure.

Kani 0.60.0 successfully verified all three shared-arithmetic harnesses:
totality over every `u128` input, exact accepted debit/credit conservation over
the admitted domain, and the insufficient/overflow rejection partition with
stable precedence. This formal evidence applies to the small arithmetic
function and its stated assumptions. It does not formally verify the typed
state, codec, hashing, effect projection, runtime adapter, or wider settlement
layer.

## Negative knowledge and nonclaims

- `expected_pre_state_root`, `expected_command_hash`, and
  `expected_authorization_subject_id` are ordinary input data. A future guest
  must bind them to an authenticated `EconomicCommandOccurrenceV1`, grant,
  nonce, profile, route, and module release.
- The whole-state hash authenticates the supplied bounded map inside this
  function. It is not a complete sparse-Merkle opening proof for durable lane
  state and does not derive `GlobalEconomicStateRootV1`.
- The movement row alone is not a reconciled `GlobalEconomicEffectPlanV1` and
  carries no settlement capability.
- Existing runtime accounts use a different public-key representation from the
  new 32-byte global account identifiers. An explicit adapter and migration
  mapping remain unresolved.
- The repository RISC0 workspace still uses 3.0.5. The whole-economy plan
  requires 3.0.6, rebuilt ELFs, governed image IDs, exact journals, and
  `Succinct` receipts. No guest was built under the obsolete baseline.
- No module release is activated, no route is mounted, and no API, CLI, UI,
  Tau, recovery, migration, legacy writer, or ZenoLedger path calls this leaf.
- This slice adds no issue, burn, fee, replay, terminal, proof, RC,
  production-readiness, formal-verification, or whole-economy authority claim.

## Next proof-worthy gap

Upgrade the governed RISC0 workspaces to exact 3.0.6 with lock and provenance
evidence. Then bind this transition to an authenticated occurrence and complete
lane-state opening statement before adding the first Asset Transfer guest. The
release-aware verifier must accept only the governed image and exact canonical
journal and must return no publication capability.
