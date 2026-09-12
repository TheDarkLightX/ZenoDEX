# Custody coordinator bundle review

Subject: `244c50ebcbed2a3fbb332d5853ce7260d989a5e2`.
Verdict: **accepted within the stated finite-model and runtime-test scope**.
This review grants no publication or release authority.

The parent integrated and verified the bundle. Independent native Astra reviewed
the proofs, fixture reuse, runtime oracle, mutation checks and score amendment.
Daybreak independently examined the actual coordinator/global/publication callers
and reproduced the coherent recipient-reroute case. Review is advisory; the
[delivery evidence](custody_coordinator_bundle_v2_20260912.json) records executable
checks and source hashes. Neither reviewer ran the parent's full test commands.

Reviewed final source hashes:

| Subject | SHA-256 |
| --- | --- |
| Coordinator outcome proof | `fb3afba8139d5dce37712cd02d2f21a739d5e01d467689a44a19824b5d88f061` |
| Coordinator trace proof | `db237f62c260b102ed0eb3544a61f35153295a16d065e554702b25a7628c378e` |
| Shared-witness controls | `a263183581797a671103fcedc903f9db9dd84e800b423d1a207dac4e7de1d58d` |
| Formal/runtime harness | `f1dd926e2060a54383ff363c767e796329c8b7fadeb158dc63d5695db3028911` |

The accepted outcomes are inhabited by actual transfer, issue and burn fixtures.
The trace theorem derives successor resource admission from the returned outcome
and includes rejection. It needs initial constructor/policy admission and command
shape; it does not assume an admitted successor at each step. Aristotle filled
three fixed proof bodies; the parent checked unchanged declarations, recompiled
under the original toolchain and audited the standard axiom set.

Runtime correspondence serializes the actual leaf independently of Lean's finite
plan and compares complete state, all six effect collections, fourteen journal
fields, source roots, and the domain plus nine-field receipt body. Finite maps
keyed by complete inputs make missing bindings visible. Ten fixed vectors and a
four-attempt mixed history pass. Two compiling completion mutants preserve the
explicit effect/state observations and fail the expected journal/receipt checks.

Daybreak's coherent Bob-to-Mallory balance/effect reroute reaches a pure proving
frame through a faulty internal leaf. Correct independent frame replay rejects
it. The new regression preserves that boundary. Conservation and a constructed
acceptance object do not authenticate command intent or a compromised process.

`SourceRefinesFinite` remains an accepted-theorem premise. Universal hashing,
parsing, schema admission, runtime/Rust correspondence, nonresource constructor
exceptions, authentic predecessors, real receipts and publication remain open.
The scope does not justify a full lane or formal-core completion claim.

The unchanged rubric receives one amendment:

| Cell | Before | After |
| --- | ---: | ---: |
| Generic transfer proof / refinement | 0.76 / 0.47 | 0.80 / 0.52 |
| Managed issue proof / refinement | 0.76 / 0.42 | 0.80 / 0.47 |
| Managed burn proof / refinement | 0.76 / 0.42 | 0.80 / 0.47 |
| W09 low / central / high | 0.22 / 0.30 / 0.40 | 0.23 / 0.31 / 0.41 |

All semantics, uncertainty labels, other capabilities, W07, shared formal rows,
and qualification scores are inherited. The formal weighted increment is
`3 * (0.4 * 0.04 + 0.3 * 0.05) / 140 * 100`, about **0.0664 pp**.
W09 adds **0.100 pp** to the separate V3 estimate. No new tracking or test count
earns additional credit. The before input is the already retained admission
assessment; only one new standalone after input is stored.
