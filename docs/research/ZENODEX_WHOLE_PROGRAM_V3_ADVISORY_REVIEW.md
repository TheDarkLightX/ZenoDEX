# Whole-program V3 coordination advisory review

Date: 2026-09-04. Verdict: **ADVISORY_ACCEPT_RESEARCH_PLAN_ONLY_WITH_LIMITS**.

Independent delegated Codex review found no blocking defect in this exact
coordination candidate for research-plan admission. The reviewer did not author
or modify the five reviewed files. The review author previously implemented a
receipt-adapter candidate; this verdict does not review or qualify that adapter.

This is an advisory verdict on plan fidelity, source binding and coordination.
It does not admit the plan into the active registry. It grants no production,
settlement, release or value-movement authority and closes zero value-movement
gates. Actual admission must bind the reviewed bytes through the existing
research-only admission process. A change to any subject below invalidates this
exact-subject verdict until reviewed again.

## Exact subject

Integration base and observed HEAD:
`c6a9fd028ded9224427a645c1217d0ce576f78af`.
Parent: `beb43baaef629276f3dae07e8e62ebc42cc3217a`.
Tree: `4610bff736c26e436c43adb66de05f0a24ae20c7`.
The five candidate files were uncommitted review inputs; their byte identities
are the subject, rather than a claim that they occur in the base tree.

| Reviewed file | SHA-256 |
| --- | --- |
| `docs/ZENODEX_COMPLETION_PLAN.md` | `2296579ca21bd3f99cf25b9b545f700209a6371e9b05fb2e5e4ccb4c906d4c3b` |
| `docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V3.json` | `e1b45e9ef9da7fa2c584567db3ac4605b6eb4ec065933b9e71be5ba82ef31adc` |
| `docs/research/ZENODEX_WHOLE_PROGRAM_V3_AUTHORITY_DISCOVERY.md` | `cb712cea2c51d26d6797eb0d1cbff3990a6d51ef9c19e41a7c2bbfbdca211e63` |
| `tools/check_whole_program_plan_v3.py` | `590a295d575e563d9377fad6dd6e603acdadb9a28a09f48ffc645d5029524311` |
| `tests/test_check_whole_program_plan_v3.py` | `ab8fad64f17d7ba899a62055b91a52daa964378a551554b11b3d20f48a3d23a8` |

The checker also reads six historical/normative Git blobs at the fixed base,
checks their SHA-256 values, and verifies the recorded parent/tree and base
ancestry. Its independent capability-manifest constant binds the 103-capability,
twelve-lane, four-route, four-exclusion floor. These source checks were replayed.

## Findings and plan fidelity

No blocking finding was identified within the reviewed scope.

- The four milestone distinctions remain explicit. SHADOW, disabled required
  features, source inventories, fixture receipts, review grades and test counts
  cannot establish whole-program completion.
- The documents retain ZenoLedger publication ownership, constrained governance
  commands, collateral-governed zUSD issuance/burn and same-occurrence ZDEX
  purchase-and-exact-burn. They retain historical wire decoding and explicit
  migration requirements.
- Pure core inputs, authenticated shell acquisition, store-current publication,
  observation isolation, logical rejection purity, all four outcome classes,
  journal sufficiency and distinct release/policy/publication identities match
  the user-supplied V3 contract.
- All fourteen work packages remain present. Early W01 investigation and
  boundary-local work are distinguished from closure dependencies. The default
  checker reports only `W00` and `W01` as eligible starts. W08 route starts remain
  conditional on named lane and publication contracts and are explicitly
  reported as `CONTRACTS_NOT_VERIFIED`.
- The 1-8 route-receipt and 1-64 epoch-command limits remain fixed. Task status
  labels and caller-supplied advisory completions do not change authority,
  production readiness, claim ceilings or promoted gate counts.
- The authority-discovery document qualifies its static review by exact base,
  retains unknown/missing writer and delivery obligations, separates SEC
  integration, and distinguishes historical G1-G14 claims from present closure.
  Its substantive external/deployment findings were reviewed for consistent
  scope here; they were not independently re-investigated as a whole-program
  audit.

## Executed evidence

```bash
PYTHONDONTWRITEBYTECODE=1 python3 tools/check_whole_program_plan_v3.py --json
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -p no:cacheprovider -q tests/test_check_whole_program_plan_v3.py
```

The checker passed with plan SHA-256
`e1b45e9ef9da7fa2c584567db3ac4605b6eb4ec065933b9e71be5ba82ef31adc`,
`eligible_next_starts=["W00","W01"]`, `production_authority="NONE"`,
`release_ready=false` and `closed_value_movement_gate_count=0`.
All **40 focused tests passed**.

An additional in-memory mutation sweep removed each enforced minimum start or
closure dependency individually: **68 deletions all rejected with
`REQUIRED_DEPENDENCY`**. Each of the five claim-ceiling coordinates was separately
changed toward completion or promotion: **five mutations all rejected with
`CLAIM_CEILING`**. Reviewed files were unchanged throughout these sweeps.

The retained suite also checks wrong source hashes, source-set shrinkage, lost
capabilities/exclusions, route-contract drift, dependency cycles, duplicate task
identities, unknown dependencies, false authority, and malformed JSON/file
inputs. A positive control marks all tasks and advisory completions complete;
the report still grants no authority or readiness. These are meaningful
coordination guard checks, not implementation-preservation proofs.

## Trust and resource limits

1. The plan file has a 131,072-byte limit and is read through the inherited
   no-follow regular-file acquisition helper. The inherited decoder rejects
   duplicate keys, floats, nonfinite numbers, invalid UTF-8 and oversized
   integers, and validates owned JSON depth/node/string budgets. Standard-library
   parsing occurs before the owned structural-budget pass. Parser recursion and
   allocation exceptions are converted to rejection, but this review establishes
   no hard CPU/RSS bound or process-isolation theorem for JSON decoding.
2. Historical Git verification trusts the local Git implementation and host.
   The inherited ports constrain environment and execution time; the blob reader
   checks its advertised size before capture. This is not a theorem of complete
   subprocess resource containment under a compromised tool or operating system.
3. The recovered external analysis and A+ design hashes are checked against
   recorded constants. This review did not reacquire their original files. The
   source-bound authority-discovery dispositions and the supplied user plan
   establish the reviewed reconciliation context; hash labels alone do not
   independently verify unavailable original contents.
4. `--completed` inputs and task statuses are advisory declarations. The checker
   does not establish that prerequisite work or route contracts were performed.
   Free-text invariants, nonclaims and evidence descriptions receive structural
   validation; this exact-file human/agent review supplies their semantic review.
5. Broad `owned_paths` identify work-package surfaces. They are not file locks or
   a collision detector. The graph explicitly requires disjoint exact-file
   implementation packets before parallel edits.
6. No release registry mutation, live balance migration, authority activation,
   remote expenditure, proof generation, deployment attestation, formal theorem
   replay or full runtime test suite occurred in this review. The reported
   broader implementation tests are outside this verdict's executed evidence.

## Next step and promotion boundary

The exact candidate is suitable for the existing **research-only plan-admission
step**, subject to that step's own source and registry checks. Keep W00-W13
closure decisions attached to their actual implementation and acceptance
evidence. Receipt qualification, complete allocation ownership, lane lifecycles,
formal/runtime refinement, publication mediation, restart/migration authority and
committed-effect delivery remain separate obligations. Production promotion and
live activation remain closed.
