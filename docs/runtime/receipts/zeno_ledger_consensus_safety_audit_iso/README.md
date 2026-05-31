# ZenoLedger consensus-safety disaster audit — negative receipt (2026-05-31)

A 3-agent read-only adversarial audit of the ZenoLedger block-validation lane
proposed several CRITICAL/HIGH consensus disaster classes. **Central confirmation
REFUTED all of them**: the safety they flagged as "missing" is enforced by node-
level composition the read-only agents could not see (they read only
`zeno_ledger_v0.py` + a few family modules, were scoped away from the signature/
quorum layer, and could not grep). This records the refutation formally per the
campaign rule that a bounded refutation is a security artifact, and so the
advisory findings are not mistaken for confirmed bugs.

> Discipline: advisory search proposes candidate disaster states; replay/checkers/
> tests decide whether they are real. None of these became a confirmed disaster
> class. No code change was made for them (fixing a non-bug would be wrong).

## Candidate findings → refutation

| Candidate (advisory) | Severity claimed | Verdict | Evidence |
|---|---|---|---|
| ZL-A-01 checkpoint binds no signatures/quorum | CRITICAL | **REFUTED (compose-required)** | `zeno_ledger_live_quorum_v0.validate_live_checkpoint_quorum_admission_v0` → `zeno_ledger_signer_registry.verify_signature_quorum_v0` enforces signer threshold + accepted weight + registry binding; node pull requires it (tests below). `validate_checkpoint_v0` in `zeno_ledger_v0` is the structural primitive only. |
| ZL-A-02 / B-1 fork-choice has no finality anchor → reorg-past-finality | CRITICAL | **REFUTED (stronger than claimed)** | `docs/ZENO_LEDGER_VALIDATOR_SCHEDULE_AND_FORK_CHOICE_V0.md`: the v0 fork-choice is *intentionally* extend-only — "a candidate tip that requires a local reorg is **rejected**." Extend-only rejects ALL reorgs, which is stronger than finality-anchored. |
| ZL-A-03 fork-choice pools across chain_ids | HIGH | **Not reachable as exploit** | `validate_header_chain_linkage_v0` enforces a single `chain_id`; the node peer path constrains chain compatibility. Primitive pooling is not fed cross-chain headers on the acceptance path. |
| ZL-A-04 headers carry no proposer id → equivocation unattributable | MEDIUM | **Refuted as silent hole; proposer-attribution is documented next-wiring** | Node acceptance REJECTS conflicting same-height tips (test below). Proposer-attribution for *slashing* is acknowledged as a "next wiring step" in the design doc — a documented roadmap item, not a silent vulnerability. |
| ZL-A-05 config_digest never bound to config | MEDIUM | **REFUTED (allowlist admission)** | `zeno_ledger_profile.py:269` rejects a checkpoint whose `config_digest` ∉ `profile.accepted_config_digests`. Config is admitted by allowlist (no derived-hash binding by design). |

## Confirming tests / evidence (already in-repo)

- `tests/integration/test_zeno_ledger_node_fork_choice.py`:
  - `test_pull_live_from_peer_rejects_missing_required_live_quorum` → `live_quorum_missing_envelopes` (quorum REQUIRED)
  - `test_pull_live_from_peer_rejects_insufficient_live_quorum` → `live_quorum_rejected` (insufficient quorum REJECTED)
  - `test_peer_check_rejects_same_height_conflicting_live_tip` → `reject_candidate`
  - `test_pull_live_from_peer_rejects_incompatible_same_height_tip` → `rejected`
- `docs/ZENO_LEDGER_VALIDATOR_SCHEDULE_AND_FORK_CHOICE_V0.md` (extend-only fork-choice; signer-quorum-on-live-headers wiring noted as next steps).

## What WAS a real gap (fixed separately)

The audit's structural reads confirmed one genuine gap the prior increment already
closed: the per-block **post_state_root / pre_state_root state-transition binding**
was absent from `zeno_ledger_v0` primitives (commits `ca607ef6`, `355b1a14`,
`c704d21a`; Codex B+). That is a primitive-layer addition; the *finality/quorum/
fork-choice* safety above is composition-layer and already enforced.

## Honest residual (documented, not a confirmed bug)

- **Evidence/rejection-receipt re-execution binding** (Codex follow-up on the
  post_state_root validator): `validate_block_state_transition_v0` binds state
  roots but not the body's `rejection_receipts` vs re-execution. A correct binding
  must re-run from cleared evidence (apply_body_transactions deep-copies + appends).
  Tracked as the next per-block completeness item.
- **Proposer-identity → slashing attribution**: documented "next wiring" in the
  design doc; conflicting tips are already rejected at acceptance.

## Scope / tooling note

Read-only agents could not run Bash/grep (bwrap broken) and were scoped away from
`zeno_ledger_signature.py` / `zeno_oracle*` / the rust core, so they did not see
the `live_quorum` / `signer_registry` / node-orchestration composition — which is
exactly why their findings required (and received) central confirmation before any
were treated as real. Net: **0 confirmed new disaster classes; ledger consensus
safety is sound via the composed acceptance path.**
