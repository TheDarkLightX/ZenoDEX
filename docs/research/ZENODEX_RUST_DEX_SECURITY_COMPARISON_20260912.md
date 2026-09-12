# Rust DEX security comparison and proof-efficiency findings

Reviewed September 12, 2026. Status: research; `NOT_RESCORED`.
ZenoDEX subject: `afb5fd52cae91077276c36653dfe95d5e163ecd9` plus the
preserved, uncommitted coordinator tests. This review changes no economic
semantics, proof claim, active plan, release authority, or completion score.

The user requested modern Rust DEX examples with a good security history,
excluding Drift as a positive security benchmark. Focused searches of project
and security sources found no publicly disclosed exploited incident for Orca
Whirlpools, Phoenix Legacy, or Manifest. This is a search result, not a proof
that an incident never occurred. A clean record must be considered alongside
deployment age, exposure, upgrades, audit scope, and remaining trust.

| Subject inspected | Why study it | Qualification limit |
| --- | --- | --- |
| Orca Whirlpools, `408c945fef4c49ab70def4303377cfaf8f0f3c99` | Rust AMM; public audits since 2022; active bounty; explicit account constraints and a separate swap calculation/update value | No whole-program formal-completeness claim established; current upgrade controls and deployed-byte correspondence not independently verified here |
| Phoenix Legacy, `5a34f7f901fd9e04057198d4fc7b7286f78b53f2` | Compact Rust CLOB; distinct units; public audits and reproducible deployed-program comparison procedure | Legacy spot program only; do not transfer its record to newer Phoenix products; bounty excludes UI and privileged-key attacks |
| Manifest, `ebf92a05b39160379dd10b1e18065423716409a0` | Rust core/wrapper separation; public executable conservation, ownership and withdrawal rules | Younger comparison; 2024 audit covers older commits; current README discloses a 4-of-5 upgrade multisig; proofs use summaries and restricted models |

Orca's [audit index](https://docs.orca.so/reference/security-audits) and
[bounty](https://immunefi.com/bug-bounty/orca/information/) document its review
program. The [Neodyme report](https://www.neodyme.io/reports/orca.pdf) identifies
and confirms fixes for inverted position ticks and swap overflow before launch.
These findings are evidence of audit and repair, not evidence of exploitation.
The pinned repository also contains August 2026 audit reports. Public audit
index dates and repository report dates differ; neither qualifies every later
commit automatically.

Phoenix's [repository](https://github.com/Ellipsis-Labs/phoenix-v1) identifies
its deployed program and build-comparison command. Its
[security policy](https://github.com/Ellipsis-Labs/phoenix-v1/security) gives
the bounty scope and exclusions. Its
[quantity types](https://github.com/Ellipsis-Labs/phoenix-v1/blob/5a34f7f901fd9e04057198d4fc7b7286f78b53f2/src/quantities.rs)
distinguish lots, atoms and conversion factors. These types reduce unit errors;
they do not by themselves prove overflow safety, caller authorization, or
correct rounding. Some operations permit unchecked conversions/arithmetic.

Manifest's [repository](https://github.com/Bonasa-Tech/manifest) places optional
trading features in wrappers and discloses upgrade authority. The
[Certora audit](https://www.certora.com/reports/manifest) reports verification
relative to specified rules and a manual review. Its
[verification notes](https://github.com/Bonasa-Tech/manifest/blob/ebf92a05b39160379dd10b1e18065423716409a0/Certora_README.md)
disclose mocked book/global state, a manually maintained matching-loop model,
and three model drifts caught while adding differential tests. Guards become
assumptions in some verification paths, so accepted-execution preservation must
not be advertised as complete rejection behavior or availability. The report's
bounded assumptions and old commits remain part of the comparison.

Drift's [April 2026 recovery disclosure](https://www.drift.trade/updates/incident-recovery-update-april-16-2026-now)
and Raydium's [December 2022 post-mortem](https://raydium.medium.com/detailed-post-mortem-and-next-steps-d6d6dd461c3e)
exclude them from a never-exploited shortlist. Administrative compromise is a
funds-safety failure regardless of whether a swap formula is correct. Repaired
protocols can still supply negative case studies.

Uniswap v2/v3 remain an additional, non-Rust longevity comparison. Uniswap's
[January 2025 announcement](https://blog.uniswap.org/uniswap-v4-is-here) reports
465 million swaps without an exploit for those versions as of that publication.
That dated statement does not certify all Uniswap versions, hooks, routers,
websites, or user signatures. The [v2 architecture](https://blog.uniswap.org/uniswap-v2)
provides a useful small-core/helper precedent, with user-facing protections
also required in the helpers.

The resulting recommendations are engineering judgments, not imported proofs:

1. Reuse one accounting and settlement implementation across applicable lanes.
   Keep per-lane authorization, rounding, solvency and terminal behavior explicit.
   A balanced transfer can still debit the wrong person. Moving an obligation
   to a wrapper does not remove it from whole-product qualification.
2. Prefer rules over actual execution functions where the tool supports them.
   Manifest's [deposit rules](https://github.com/Bonasa-Tech/manifest/blob/ebf92a05b39160379dd10b1e18065423716409a0/programs/manifest/src/certora/spec/funds_checks.rs)
   call the processor core and compare before/after funds and trader effects.
   Avoid another independent model when a supported source-derived connection
   can provide the required evidence with fewer maintenance obligations.
3. Evaluate an existing Rust-to-proof route on one current command before any
   migration. [Aeneas](https://github.com/AeneasVerif/aeneas) translates Rust MIR
   through Charon and supports Lean; [Verus](https://verus-lang.github.io/verus/guide/)
   verifies annotated Rust with SMT. Both have supported-subset and trusted-tool
   limits. Neither was installed, run, or qualified in this research. The trial
   must preserve exact arithmetic, bytes, reject precedence and effect behavior.
4. Reuse platform guarantees through a pinned boundary contract. Solana supplies
   [atomic transaction state rollback](https://solana.com/docs/core/transactions),
   while failed transactions still pay fees. A ZenoLedger fallback must implement
   and qualify its own publication/recovery contract once; each economic lane
   should then rely on that shared contract. A Tau/finality adapter alone does
   not establish those guarantees.

The historical ZenoDEX review found no recoverable original RC3 whole-product
release subject in the refs/history searched. The tracked
[preservation manifest](ZRPF_FCIS_PRESERVATION_MANIFEST_20260811.md) is explicitly
unmounted; its [receipt evidence](ZRPF_SHAPEFORGE_GLOBAL_EPOCH_ADMISSION_V1.md)
qualifies a narrow leaf/coordinator computation. This does not establish that
the user's earlier product did not exist. It prevents equating that label with
V3's broader denominator. Existing CPMM and other mathematics remains reusable
where definitions and premises match. FCIS alone invalidates no theorem.

There is a real efficiency problem to correct: the existing
[simplification review](ZENODEX_SIMPLIFICATION_REVIEW_20260908.md) identifies
repeated representations and an older publisher/newer-leaf integration split.
The next implementation remains the coherent coordinator outcome/effect/runtime
bundle specified in [session continuity](../ZENODEX_SESSION_CONTINUITY.md).
This research authorizes no removal of required workflows or historical decoding,
and does not replace that acceptance target with a tooling project.

Root inspected pinned source and primary reports. Independent native security
review screened the three Rust candidates; independent historical review
examined RC labels, reusable proofs and denominator scope. A 1,268-entry public
incident-registry lookup was used only as a discovery aid. No external prover,
deployed-byte verification, chain upgrade inspection, or foreign-project build
was run. Research adds no automatic implementation or qualification credit.

Validation: `git diff --check` and the new note's whitespace/fence checks pass.
`python3 tools/check_claims_registry.py` fails on the existing claim 123 reference
to missing `tools/check_derivatives_authorization_matrix.py`. The registry and
that disputed historical evidence were not modified to clear the gate. No
runtime, Lean, Kani, ESSO, RISC0, or release qualification was run for this
documentation-only change.
