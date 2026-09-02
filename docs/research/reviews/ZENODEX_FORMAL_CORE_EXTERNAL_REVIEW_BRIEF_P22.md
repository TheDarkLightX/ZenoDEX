# External review brief — ZenoDEX formal-core campaign, candidate C8''''' (P22)

Audience: an external reviewer (GPT 5.6 or equivalent) with no prior context.
Prepared: 2026-09-02. Authority of everything under review: NONE. `formal_core_complete: false`.

## Where the work is

- Repository: `github.com/TheDarkLightX/ZenoDEX` (private)
- Branch: `codex/formal-core-fable-20260901`
- Review target (exact hashes; review AT these, not at the branch tip):
  - Subject **S22** = `b0c6d1d0f20b99ef4afc036653fd3cec340c7781` (the source commit)
  - Packet **P22** = `fd1e2fbe241ca31aba68d3747dd763de11197366` (artifact-only direct child; changes only
    `docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.{json,md}`)
  - Tag: `formal-core-c8p5-p-candidate-20260902`

## What this campaign is

A review-gated hardening chain for the O-008 formal-cycle admission surface of a
research DEX settlement core (functional core / imperative shell, validate-before-mutate,
closed reject codes, checked u128, canonical ordering, no floats/hash()/assert in core).
Every candidate is one source commit S plus one packet-freeze commit P; an independent
reviewer (Claude Opus) reviews at the exact P hash; findings become the next child
candidate; each review receipt is committed verbatim. Grade trajectory across the last
five candidates: C+ (P18) -> B (P19) -> B+ (P20) -> A- (P21) -> P22 under review.

## What to review

Primary subjects (all paths at S22):

| Surface | Files |
|---|---|
| Admission checker (pure core / shell / CLI / builder) | `tools/o008_formal_cycle_admission_v1.py`, `tools/o008_formal_cycle_shell_v1.py`, `tools/check_o008_formal_cycle_v1.py`, `tools/build_o008_formal_cycle_v1.py` |
| The frozen evidence packet (v15 schema) | `docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.{json,md}` at P22 |
| Allocation certificate + lane producers (Python + Rust twins) | `src/core/global_accounting_allocation_certificate_v1.py`, `src/core/global_accounting_lane_producers_v1.py`, `zk/global_settlement_abi_v1/src/global_accounting_{allocation_certificate,lane_producers}.rs` |
| Shared bound constants + total Python/Rust parity | `src/core/global_settlement_types_v1.py:27-52`, `zk/global_settlement_abi_v1/src/canonical.rs`, `tests/core/test_global_settlement_abi_v1_resource_bounds.py` |
| Gated test surfaces | `tests/test_check_o008_formal_cycle_v1.py` (389 tests), `tests/core/test_global_accounting_lane_producers_v1.py` (30), `tests/formal/test_esso_global_settlement_core_v1.py` (136), the two Lean gates |
| Review receipts (the full audit trail) | `docs/research/reviews/ZENODEX_FORMAL_CORE_P1[6-9]_OPUS_REVIEW_*.md`, `..._P2[01]_OPUS_REVIEW_*.md` |

Suggested review order: read the P21 receipt (grade A-, three P3 findings), then verify
the S22 diff against its three claimed repairs (total parity, mirror-block placement,
documented-and-pinned non-total boundary), then hunt for what both reviewers missed.

## Review modes

**Static (no execution needed):** check out P22, read the packet JSON against the source
it pins (every `source_pins` row carries the git blob and sha256 at S22), audit the
checker's fail-closed logic, the closed reject-code families, the claim ceiling
(`claim_ceiling`, `nonclaims` — every authority must be NONE, 0/12 value-movement gates),
and whether any English claim in packet/docstrings/THV1 packets overstates what the code
enforces. Overclaim-hunting has been the highest-yield review activity in this campaign.

**Replay (if you can execute):** clone, check out P22, then:

```bash
python -m venv .venv && .venv/bin/pip install -r requirements-dev.lock.txt
PY=.venv/bin/python
"$PY" tools/check_o008_formal_cycle_v1.py --root "$PWD"            # expect exit 0, NOT_RUN
"$PY" -m pytest -q tests/test_check_o008_formal_cycle_v1.py        # expect 389 passed
"$PY" -m pytest -q tests/core/test_global_accounting_lane_producers_v1.py   # 30 passed
cd zk/global_settlement_abi_v1 && cargo test --locked && cargo clippy --locked --all-targets -- -D warnings
```

Full replay (`--replay`, 28 commands incl. two-solver ESSO and Lean gates) additionally
needs ESSO (z3+cvc5) and a Lean4/mathlib toolchain; the packet's `proof_replay.commands`
lists every command with its expected comparable. Run the two Lean gates serially.

## Constraints that must hold

- The claim ceiling must not move: `formal_core_complete=false`, all seven authority
  fields NONE, `value_movement_gates_closed 0/12`, `o008_status OPEN_EXACT_ALL_12_RECONCILIATION_MISSING`.
- No lane producer is REGISTERED receipt-backed; the implemented wave-B producer is on no
  acceptance path (registry keeps ASSET_TRANSFER at NO_PRODUCER until C9 receipt admission).
- Evidence packets under `tests/evidence/test_hygiene/` are append-only lineages.

## Deliverable

Grade A..F with findings ranked P1 (fail-closed violation / claim-ceiling breach /
unsound admission) > P2 (false or self-contradicting claim in pinned prose) > P3
(coverage gap, drift channel, maintainability). For every finding: exact file:line at
S22/P22 and a minimal reproduction. Bounded refutations ("I looked for X and it is
absent") are valued deliverables, not filler.
