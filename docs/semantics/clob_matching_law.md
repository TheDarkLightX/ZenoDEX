# CLOB Matching-Law Claim (Stage 2 proof-carrying orderbook)

This is the prose front door for the CLOB matching-law consensus claim — carried by
the `clob.place_limit_order` operation — in the same spirit as
`zenodex_consensus_semantics_v1.md` (perps). It states, honestly, what the RISC0
CLOB guest proves and what is deferred.

The MACHINE-CHECKED entry is now LIVE: the `clob.place_limit_order` operation block
in `config/semantics/zenodex_consensus_contract_v1.json`, validated by
`tools/semantics/check_consensus_semantic_contract.py` (linter:
`6 scenarios, 6 executable, 0 open obligation(s)`), with
`docs/semantics/clob_orderbook_guest.feature` bound in
`tests/semantics/test_zenodex_consensus_bdd.py`, plus an overclaim guard on
`src/integration/orderbook_api.py` forbidding a `PROOF_VERIFIED` status at Stage 0.
This doc is the prose companion; the machine entry is the enforced contract.

## Operation

`clob.place_limit_order` — a single incoming taker matched against a resting CLOB
book under price-time priority (continuous match). Scope (Stage 2 initial, per
`proof_carrying_orderbook_build_spec.md`): one market, limit orders, price-time
priority, bounded event batches, no hidden order types.

The Stage 2 law: **"No higher-priority eligible order was skipped for any accepted
fill."**

## Claim level: `core_equivalent`

Against the contract taxonomy (`core_equivalent` < `modeled_envelope_equivalent` <
`live_replay_authority_equivalent` < `live_equivalent`), the honest level is
**`core_equivalent`**: the guest's matching is byte-exact with the live Python
matching core (`src/core/clob_matching.py::apply_order`).

It is NOT `live_equivalent`: the deployed orderbook admission
(`src/integration/orderbook_api.py`, a Stage-0 in-memory store) runs `apply_order`
but does NOT invoke or require the guest proof. The replay levels do not apply —
the matching law has no replay-authority concept.

## Additional honesty properties (recorded, not a higher tier)

These are stronger than the perps surface, but they are properties of the proof,
not a higher equivalence tier:

- **Ledger-exact book root, by construction.** `ClobBookV1::state_root` reproduces
  `src/state/clob_book.py::ClobBook.state_root` BYTE-FOR-BYTE (ported canonical
  encoders), so the guest proves the ACTUAL ledger book root — there is NO
  encoder-equivalence obligation (unlike the perps guest's private hashing).
- **A real STARK.** `clob_cli_prove_verify_smoke` (default_prover, ~31s) proves the
  transition, the receipt verifies against the pinned image id, AND tampered
  bindings are rejected.
- **Cross-language-pinned encodings.** Every guest-defined encoding (book root,
  matcher output, `matching_rule_hash`/`fee_rule_hash`, `event_log_root`) has a
  Python mirror and a cross-language parity fixture/test. This is load-bearing: a
  5-skeptic adversarial review caught that the Rust rule-hash labels had silently
  drifted from the ledger (`orderbook_api.py`), which would have made the client
  reject every proof. Rule: no guest-defined encoding without a pinned mirror.
- **Honest fees.** The v1 matcher takes no fee; `fee_total = 0` and
  `fee_rule_hash` commits `stage0_zero_fee_stub`. The quote floor is
  conservation-exact (symmetric quote), not a hidden fee.

## Deferred obligation (the `live_equivalent` gap)

`live_equivalent` requires the deployed orderbook admission to require/verify the
guest proof (proof-carrying admission + journal bound to the ledger header
post_state_root). That is **Stage 3 (trustless client finality)** — the matching
law is proven; making the deployed path refuse the unproven is the remaining work.

## Evidence

- Guest + transition: `zk/state_proof_risc0/shared/src/clob.rs`,
  `methods/guest/src/main.rs` (`ZenoProofInputV1::Clob`).
- Parity: `cli/tests/clob_book_root_parity.rs`, `clob_match_parity.rs`;
  `tests/core/test_clob_matching_law.py`, `test_clob_*_fixture.py`.
- Real proof: `cli/tests/clob_cli_prove_verify_smoke.rs`.
- Commits: I1 `082e6a06`, I2 `6a7c11f1`, I2b `f2ec56a9`, I2b-fix `c84c2c5c`,
  I4 `bccca5ae`, I3 `81720be9`.

## Machine-checked entry (done)

The claim is encoded in the gated contract: the `clob.place_limit_order` operation
block in `zenodex_consensus_contract_v1.json` (claim_level `core_equivalent`;
`deployed_api_admission_binding_status: not_bound_stage0_api_does_not_invoke_guest`;
`strongest_allowed_claim: core_equivalent`), the `clob_orderbook_guest.feature`
scenario `clob.place_limit_order.guest.claim_scoped_to_matching_core` bound in
`test_zenodex_consensus_bdd.py`, validated by the linter
(`6 scenarios, 6 executable`), plus an overclaim guard on `orderbook_api.py` that
forbids a `PROOF_VERIFIED` status at Stage 0. The remaining `live_equivalent` gap —
wire the deployed admission to require/verify the proof — is Stage 3.
