# WS2 — Trustless Refuse-by-Default Client Loop

> "Trust the MATH, not the hosts. If the host must be honest, it has failed."

This is the heart of the trustless-hosting thesis: **validity is a precondition of
acceptance, not something a host asserts.** A trustless client does not believe a
host's claimed `ACCEPT`; it independently decides `ACCEPT`/`REFUSE` by checking that a
**real proof binds the right statement**, fail-closed. The host is a relay; liveness
comes from multiplicity (many hosts), not from any one being honest.

## Status / scope (read first — do not overclaim)

What is **done**: the client decision **loop** — the ordered fail-closed gates, the full
refuse taxonomy, and the non-trust discipline — is implemented as a pure core and
**adversarially tested** (31 tests; ACCEPT + every REFUSE code + the red-team attacks).

What is **NOT done, and the trust therefore rests on**: the two impure ports are
**specified but unimplemented stubs**:
- `ReceiptVerifierPort` — the real RISC0 `receipt.verify` against the client-pinned
  image id + the blessed-verifier identity check. The tests inject a fake that returns
  `VERIFIED` by fiat, so every gate below #3 is exercised over *assumed-proven* bytes.
- `RebindFn` — the canonical-encoder mirror that recomputes `operation_hash`,
  parity-tested against the guest.

**Until both ports are real and parity-tested, this provides NO live trust guarantee** —
it certifies the *loop*, not refuse-by-default itself. Likewise, the anti-double-accept
property holds only if the imperative shell applies the emitted `HeadAdvanceObligation`
(the pure core cannot enforce it). Do not describe WS2 as "trustless refuse-by-default
shipped"; describe it as "the decision loop, tested over a stubbed verifier."

## Deliverable

`src/integration/client_admission_decision.py` — the **pure functional core** of the
client decision: `decide_admission(...) -> AdmissionDecision`. The only impure
dependency (verifying a RISC0 receipt) is an injected `ReceiptVerifierPort`, so the
core is deterministic and exhaustively testable. Corpus:
`tests/integration/test_client_admission_decision.py` (ACCEPT path + every REFUSE code
+ the red-team attacks; 30 tests).

This is a **client-side reference policy**. It does not edit the deployed admission
path (`orderbook_api.py`), the JS proof-client, or the SDK — those mirror this
canonical policy. (Wiring the deployed path to require it is Stage 3 / a later step.)

## Design provenance

Synthesized by a 17-agent design workflow (understand → 3-lens design panel → 8-vector
adversarial red-team → synthesis) and **grounded against the real Rust journal structs**
(`zk/state_proof_risc0/shared/src/{surfaces,clob}.rs`) and the consensus-semantics
contract (`config/semantics/zenodex_consensus_contract_v1.json`).

## The non-trust clause (load-bearing)

No field **asserted by the host** is ever an `ACCEPT` input:
`host_response.ok / proof_status / status / production_security_claim / is_final /
promotion_ready / artifact_binding_complete`, and the proof/journal's own *claimed*
image_id and chain_id, are untrusted hints. The only trusted inputs are the
client-shipped **pinned registry** and the client-trusted **contract**. This directly
closes a fake-green trap the red-team found: `proof_verifier.py` only reads `ok` and
never validates `production_security_claim`, so a verifier could echo it `True` — the
client therefore never reads it.

## The ordered, fail-closed gates

The first failing gate returns `REFUSE(stable_code)` and performs **no mutation**
(reject-is-no-op). `ACCEPT` is the positive conjunction of all gates.

| # | Gate | Refuse code | Why it's needed |
|---|------|-------------|-----------------|
| 0 | Resolve client pins + contract row (reads nothing from host) | `UNMAPPED_OPERATION` | No trust root → refuse |
| 1 | Proof present | `NO_PROOF` | Stage-0 `proof_pending`; host-claims-verified-but-no-proof |
| 2 | Verifier identity pin well-formed (absolute binary, no PATH lookup) | `VERIFIER_NOT_PINNED` | Echo/wrapper verifier substitution |
| 3 | **Real STARK verify against the client-pinned image id** | `RECEIPT_VERIFY_FAILED` | Echo/wrapper (no real STARK); self-certifying guest (verify against *client* pin, not the proof's) |
| 4 | `proof_type` exact match | `PROOF_TYPE_MISMATCH` | Cross-surface reuse; weaker-lane substitution (journal carries no claim-level field) |
| 5 | image id echo: non-zero & == pin (defense-in-depth, never replaces #3) | `IMAGE_ID_MISMATCH` | Zero/forged echoed image |
| 6 | `chain_id` == client pin (host-independent) | `CHAIN_ID_MISMATCH` | Cross-chain / testnet→mainnet replay of a valid proof |
| 7 | `pre_app_hash_present == True` **then** `pre_app_hash == head` | `PRESTATE_UNBOUND` / `PRESTATE_MISMATCH` | The guest skips the pre-root binding when `present==False` yet echoes the attacker's `pre_app_hash` (`surfaces.rs:331/422`) — the flag must be checked first |
| 8 | Recompute `operation_hash` from the **requested** op | `OPERATION_MISMATCH` | Replay a real cheap-op proof (amount=1) for a requested expensive op (amount=1000) |
| 9 | Complete bindings over the **closed** required-field set: present-and-non-null **then** equality | `BINDING_INCOMPLETE_OR_NULL` / `BINDING_MISMATCH` | An omitted/null expected field silently skipped (drive off the closed set, not the supplied map); rule-hash / root drift |
| 10 | Claim floor & ceiling via **two independent lookups** | `CLAIM_TOO_WEAK` / `CLAIM_OVERCLAIM` | Weaker-than-required claim; scope inflation. Two lookups → non-tautological |
| 11 | Admission threshold + proof-gating | `ADMISSION_NOT_PROOF_GATED` | A valid `core_equivalent` CLOB proof is correct-but-not-admissible (Stage-0 API does not invoke the guest) |
| 12 | **ACCEPT** + emit head-advance obligation | — | The shell must apply `{new_head, retire_preroot}` so a valid proof cannot be re-accepted (defeats stale replay) |

## What this does NOT claim (honesty)

- **Liveness** — an honest client must still make progress; the `head_advance`
  obligation is how, and refuse-by-default must not deadlock honest clients.
- **Oracle honesty / true market price** — see `ORACLE_TRUST_POSTURE.md` (L2).
- **Data availability / ordering** — separate trust component.
- **Economic desirability** — it proves a *valid* transition, not a *good* one.

It proves only: a real proof, for **this** operation, at or above the required claim
level, bound to the client's head and pins.

## Remaining work

- A production `ReceiptVerifierPort` (real RISC0 `receipt.verify` against the pinned
  image id + the blessed-verifier identity check) and a production `RebindFn` (the
  canonical-encoder mirror, parity-tested against the guest) — both overlap the proof-
  client zone; wire under coordination.
- Mirror this policy in the JS proof-client and gate the deployed admission path on it
  (Stage 3 / `live_equivalent`).
