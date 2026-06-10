# WS2 — Trustless Refuse-by-Default Client Loop

> "Trust the MATH, not the hosts. If the host must be honest, it has failed."

This is the heart of the trustless-hosting thesis: **validity is a precondition of
acceptance, not something a host asserts.** A trustless client does not believe a
host's claimed `ACCEPT`; it independently decides `ACCEPT`/`REFUSE` by checking that a
**real proof binds the right statement**, fail-closed. The host is a relay; liveness
comes from multiplicity (many hosts), not from any one being honest.

## Status / scope (read first — do not overclaim)

What is **done**: the client decision **loop** (the ordered fail-closed gates, the full
refuse taxonomy, the non-trust discipline), **plus both impure ports made real**, the
**imperative shell** that enforces head-advance, and the **multiplicity** layer — wired
end-to-end and proven over a **real RISC0 STARK** (perps-NP deposit: prove ~58s,
verify+decide ~0.06s, 269 KB receipt).

The two ports are no longer stubs:
- `ReceiptVerifierPort` → `Risc0CliReceiptVerifierPort`
  (`src/integration/risc0_receipt_verifier_port.py`): sha256-pins the blessed CLI binary
  (absolute path, no PATH lookup) **before** running it, drives the new
  `tau_state_proof_decode_journal` CLI command which calls
  `receipt.verify(GUEST_ID)` **before echoing any journal byte**
  (`zk/state_proof_risc0/cli/src/decode_journal.rs`), enforces the **client** image-id
  pin against the verifier's compiled-in identity (not the proof's claim), and parses the
  journal **closed-shape per proof_type**. UNKNOWN/TIMEOUT/ERROR are distinct and all
  fail closed.
- `RebindFn` → `perps_np_deposit_rebind` (`src/integration/perps_np_rebind.py`): a total,
  no-raise canonical-encoder mirror of `surfaces.rs`, **parity-tested byte-for-byte**
  against real guest journals (golden + live `tau_state_transition_execute`).

The shell (`src/integration/client_admission_loop.py`) holds the client head and applies
the `HeadAdvanceObligation` **atomically under a lock**, so two racing submissions of one
valid proof yield exactly one ACCEPT (the second refuses at gate 7). `MultiHostAdmissionClient`
adds liveness-via-multiplicity: a withholding or corrupting host is routed around, never
trusted harder; running out of hosts is a liveness failure, **never** an acceptance.

**Honesty that survives the wiring**: with the **production** pinset (admission allow-list
EMPTY) a fully valid real proof still **REFUSES** with `ADMISSION_NOT_PROOF_GATED` —
refuse-by-default is the truthful state until Stage 3 proof-gates a deployed admission
path. The full ACCEPT mechanics are exercised only under the clearly-labelled
`--demo-stage3` pinset. What is still **NOT** trustless: DA/ordering trust for the
client's *initial* head (genesis/checkpoint is supplied, not proven here), oracle honesty,
and the production pin-distribution channel (the local generator is trust-on-first-use by
construction and says so). The trust now rests on: the real RISC0 verifier soundness +
image-id pin, the blessed-binary sha256 pin, and the encoder parity tests.

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
| 12 | Head strictly progresses (`post != head`) **then** ACCEPT + emit head-advance obligation | `HEAD_NONPROGRESS` | A `post == pre == head` transition does not move the head, so it re-passes gate 7 forever (anti-double-accept silently breaks); refuse it. The shell must apply `{new_head, retire_preroot}` so a valid proof cannot be re-accepted, and additionally refuses advancing into an already-**retired** root (the `Hk → … → Hk` cycle the pure core cannot see) |

## What this does NOT claim (honesty)

- **Liveness** — an honest client must still make progress; the `head_advance`
  obligation is how, and refuse-by-default must not deadlock honest clients.
- **Oracle honesty / true market price** — see `ORACLE_TRUST_POSTURE.md` (L2).
- **Data availability / ordering** — separate trust component.
- **Economic desirability** — it proves a *valid* transition, not a *good* one.

It proves only: a real proof, for **this** operation, at or above the required claim
level, bound to the client's head and pins.

## Wiring map (what to run)

- Build the blessed CLI: `cargo build --release` in `zk/state_proof_risc0` →
  `target/release/tau-state-proof-risc0-cli` (new subcommands:
  `tau_state_proof_decode_journal`, `tau_state_proof_verifier_identity`).
- Author a local-dev pinset: `python3 tools/gen_ws2_client_pinset_local.py --out <path>`
  (add `--demo-stage3` to exercise ACCEPT). Trust-on-first-use; **not** a production
  distribution channel.
- Load the trust roots: `load_consensus_contract()` + `load_pinned_registry(<path>)`
  (`src/integration/client_pinned_registry.py`; both fail closed on malformed input).
- Drive it: `ClientAdmissionLoop(...).submit(...)` or `MultiHostAdmissionClient(...)`.
- Real-STARK evidence: `ZENODEX_WS2_E2E=1 pytest tests/integration/test_ws2_refuse_loop_e2e_risc0.py`.

## Remaining work

- **Stage 3 (`live_equivalent`)**: gate a deployed admission path (`orderbook_api.py` /
  the perps wallet path) to REQUIRE this proof, and flip a pinset's
  `admission_proof_gated_statuses` on only when that wiring is real. Until then the
  production posture is honest refuse-by-default.
- **Production pin distribution**: replace the trust-on-first-use local generator with a
  signed-release / WS5 upgrade-gated channel that pins verifier identity + image id +
  module-versions digest.
- **More surfaces**: the perps-NP deposit rebind is the worked example; zUSD and CLOB
  rebinds + pins follow the same parity-test recipe.
- **JS proof-client parity**: mirror this canonical policy in
  `tools/dex-ui/src/sdk/zenoProofClient.js` (the WS5-A pinset already lives there).
- **Initial-head trust**: bind the client's starting head to a DA/finality checkpoint
  (currently supplied as trusted genesis/checkpoint).
