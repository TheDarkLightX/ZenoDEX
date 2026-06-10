# Oracle Trust Posture (WS4)

The trustless-hosting north star is "trust the MATH, not the hosts." The price
oracle is the **third trust assumption** (after host=relay and governance). This
doc states, honestly, *where the ZenoDex oracle actually sits* on the de-trust
spectrum — so it is never overclaimed as trustless. It is the oracle analogue of
the consensus-semantics front door's claim-level discipline.

Important framing correction: the oracle is **not** an undefended single-trusted
key. It is already trust-MINIMIZED and honestly scoped (see evidence below). WS4 is
therefore not "add de-trust" — it is "name the level honestly and define the
research gap to the next level."

## De-trust levels

| Level | Meaning | Trust required |
|---|---|---|
| **L0** `single_trusted_signer` | one pubkey publishes; you trust it | full trust in one party |
| **L1** `quorum_attested` | k-of-n signers must attest a price; no single signer suffices | trust the *quorum* (collusion ≥ threshold) |
| **L2** `quorum_attested_honest_scope` | L1 + fail-closed authorization + replay-bound receipts + **explicit non-claims** (does not assert the price is true/source honest) | same trust as L1, but the *claim* is honest about what it does NOT prove |
| **L3** `proof_carrying_provenance` | the price carries a **proof of its derivation** (e.g. a ZK proof over signed exchange data, or an on-chain TWAP the client recomputes) — the client need not trust the signers' *honesty*, only the named source data | trust only the *source data*, not the signers |
| **L4** `fully_trustless_feed` | price derived entirely on-chain; no off-chain trust | none (likely infeasible for external prices) |

## Where the ZenoDex oracle actually sits: **L2**

Evidence in the running code (not aspirational):

- **Quorum, not single key** — `src/integration/zeno_oracle_authority.py`: an active
  signer registry with `threshold >= 2` is required (the preflight *gaps* the
  surface otherwise), verified by `verify_signature_quorum_v0`. So no single signer
  can move the price. → **L1**. The median_3 aggregate lane carries the same
  property end-to-end: `tools/zenodex_oracle_admitted_median3.py` rejects an
  aggregate (`duplicate_reporter_pubkey`) when any two of the three inputs are
  signed by the same BLS key, even under distinct `reporter_id` labels or a
  re-encoded (prefix/case-variant) pubkey — so one key cannot masquerade as the
  quorum. This is a *key*-distinctness guarantee:
  distinct signing keys are **not** proof the operators behind them are
  independent (that nameable assumption is the L3 gap below), which is exactly
  why `does_not_claim_source_honesty` survives.
- **Explicit non-claims** — the same module hardcodes
  `does_not_claim_true_market_price`, `does_not_claim_source_honesty`,
  `does_not_claim_tau_consensus_finality`. The oracle's own authority profile
  refuses to assert the price is correct or the source honest. → **L2** (honest scope).
- **Fail-closed** — `src/integration/zeno_oracle_fail_closed_config.py`; staleness
  gating in `src/core/oracle.py` (`max_staleness_seconds`, `is_fresh`): a stale or
  unauthorized price is rejected, not silently used.
- **Replay-bound + proof-required flags** — required `oracle_receipt_replay_required`
  and `zk_or_proof_required`, plus external-signer / key-manager / device-approval
  flags, gate production authority.
- **Purpose-scoped authorization** — separate
  settlement/routing/trigger authorization modules: an oracle authorized for one
  purpose is not implicitly authorized for another.

So the honest claim is: **L2 — quorum-attested, fail-closed, replay-bound, and
explicit about NOT claiming the price is the true market price or the source
honest.** That is trust-MINIMIZED, not trustless.

## The gap to L3 (proof-carrying provenance) — research-scale

L3 removes trust in the signers' *honesty*. It requires the price to carry a proof
that it was *derived* from named source data, e.g. one of:

1. **ZK-over-signed-data** — a proof that the published price is a deterministic
   function (median/TWAP) of N exchange responses each signed by the exchange's
   own key. Trust shifts from "the oracle signers are honest" to "the exchanges
   signed this data" — a weaker, nameable assumption.
2. **On-chain TWAP recompute** — derive the price from on-chain DEX state the client
   can recompute. Removes off-chain trust but only works for on-chain-liquid pairs
   and inherits DEX-manipulation risk (cf. the withdrawn TWAP W² claim in the zUSD
   work — pool depth, not window length, is the lever).
3. **TEE-attested derivation** — a hardware attestation that the derivation ran
   unmodified. Trust shifts to the TEE vendor (see CONFIDENTIAL_EXTENSIONS).

Each is a real research/build effort, not a quick increment. None is built today —
and the oracle's non-claims correctly DECLINE to assert L3.

## The rule (do not overclaim)

Until an L3 proof path ships, **no surface may describe the oracle price as
trustless, proven, or "the true market price."** The oracle is L2. Any UI/docs/
release-gate language asserting otherwise is an overclaim and should fail review —
the same discipline the consensus-semantics front door enforces for guest claims.
