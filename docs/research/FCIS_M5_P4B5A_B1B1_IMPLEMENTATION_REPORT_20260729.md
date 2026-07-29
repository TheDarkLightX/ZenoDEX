# FCIS M5-P4B5A B1B-1 implementation report

```text
status: IMPLEMENTED_UNMOUNTED_REVIEW_PENDING
checkpoint: B1B-1
implementation code head before this report:
  c396fc4e92ceff8c099d7d2c7fca1532a5ec370b
approved Revision 3.4 target:
  a8b9d191b91a3258e3d7857784bbd6067a0463e1
approved Revision 3.4 packet:
  1665e788a4c4daf43982262c307d0c04b914d89b
approved verdict:
  APPROVE_B1B1_REVISION_3_4_UNMOUNTED
approved Revision 3.4 document SHA-256:
  cae6562b5e0cade2a03827a2a8f591561317b6cf684de4d22d726c25917108c5
```

## Result

B1B-1 implements the three approved untrusted carrier families:

```text
FCISAuthorityHeaderV2
DeploymentBootstrapAnchorClaimV2
V1ToV2MigrationManifestV2
```

The checkpoint also implements closed field registries, strict Python
admission, canonical Python and Rust encoders, domain-separated audit roots,
shared positive and negative vectors, and a fail-closed unmounted-scope
checker.

No runtime authority was mounted.

## Invariant and authority boundary

The implemented relation is:

```text
untrusted source or bytes
  -> closed structural admission
  -> exact immutable carrier
  -> canonical bytes
  -> optional audit root
```

The result remains untrusted data. It cannot construct:

```text
pinned deployment verifier
verified migration authority
migration candidate or successor
committed V2 state
state-bound configuration
configuration update
transition cause or evaluation candidate
receipt, decision, outbox plan, or commit bundle
proof input
publication
runtime mount
```

The migration manifest deliberately admits structurally exact values outside
the later semantic constants. For example, source snapshot version `3` remains
a carrier value and never becomes migration authority in B1B-1.

## Implemented surface

Python:

```text
src/core/fcis_b1b_authority_values.py
src/core/fcis_b1b_authority_schema.py
src/core/fcis_b1b_authority_admission.py
src/core/fcis_b1b_authority_codec.py
```

Rust:

```text
rust-runtime/crates/zenodex-runtime-core/src/fcis_b1b_authority.rs
rust-runtime/crates/zenodex-runtime-core/src/lib.rs
```

Evidence:

```text
tests/core/test_fcis_b1b_authority_values.py
tests/core/test_fcis_b1b_authority_admission.py
tests/core/test_fcis_b1b_authority_golden.py
tests/core/test_fcis_b1b1_carriers.py
tests/fixtures/fcis_b1b_authority_v2_golden.json
tools/build_fcis_b1b_authority_v2_golden.py
tools/check_fcis_b1b_revision34_contract.py
tests/tools/test_check_fcis_b1b_revision34_contract.py
.github/workflows/fcis-b1b-revision34.yml
```

The functional core contains no filesystem, network, wall-clock, environment,
or randomness read. The fixture builder and review tooling remain outside the
functional core.

## ATDD evidence

The ready B1B-1 acceptance cases were replayed from the repository root with
`PYTHONPATH` removed where applicable.

| Acceptance | Result | Evidence |
| --- | --- | --- |
| ATDD-B1B1-001 | closed | Revision 3.4 SHA-256 remains exact; the structural checker pins the immutable blob |
| ATDD-B1B1-002 | closed | direct script and module commands pass with `PYTHONPATH` absent; 21 ATDD checker tests pass |
| ATDD-B1B1-003 | closed | 2 schema scenarios pass; unknown, missing, duplicate, and trailing fields reject |
| ATDD-B1B1-004 | closed | 6 Python U256 cases and 1 Rust boundary test pass |
| ATDD-B1B1-005 | closed | 9 identifier, Unicode, and digest boundary scenarios pass |
| ATDD-B1B1-006 | closed | source-current fixture passes; 3 Python golden tests and 2 Rust golden tests pass |
| ATDD-B1B1-007 | closed | 2 carrier-only authority-boundary scenarios pass |
| ATDD-B1B1-008 | closed | structural checker is green and premature-authority mutants reject |
| ATDD-B1B1-009 | closed | integration ownership gate accepts all 26 implementation paths from the approved packet |
| ATDD-B1B1-010 | closed | 938 Python/Rust runtime files scanned with zero carrier consumers outside the allowlist |
| ATDD-B1B1-011 | closed | 14 bounded mutants pass without a repository copy |
| ATDD-B1B1-012 | ready | exact-head packet builder and documentation are part of the review target; the child packet commit closes this case |

Focused aggregate evidence:

```text
91 Python carrier, B1A-regression, ATDD, and mutation tests passed
18 P4B5A authority-snapshot tests passed, 334 deselected
3 Rust B1B carrier tests passed
Rust formatting passed
Rust clippy with -D warnings passed
focused Ruff checks passed
GitHub workflow permission check passed with zero findings
```

## Preserved counterexamples

The ATDD loop preserved these minimized failures before repair:

1. The golden source-current test failed under an environment with
   `PYTHONPATH` removed because it invoked the builder as a file. Module-form
   execution repaired the hidden import dependency.
2. The ATDD ownership checker rejected the ignored, untracked structural test.
   Force-adding that exact evidence file repaired the ownership boundary.
3. A full-repository `shutil.copytree` mutation harness was rejected by the
   execution contract. The implemented harness copies exactly the checker's 15
   declared required paths and enforces a two-megabyte bound.
4. Premature pinned-verifier types, bare-header advance helpers, public Rust
   carrier fields, out-of-scope authority paths, runtime carrier imports,
   schema/root drift, and missing required evidence each kill a named
   structural test.

## Canonical and cross-language contract

Python and Rust share:

```text
three exact schema identifiers
closed field projections
U256 range 0 through 2^256 - 1
positive configuration-version rule
bounded nonempty Unicode scalar identifiers
lowercase 0x-prefixed 32-byte digests
canonical JSON envelopes
domain-separated SHA-256 roots
shared accepted and rejected fixture cases
```

Boolean and negative integer cases are Python-only because Rust `BigUint`
cannot represent them. The shared fixture records that exclusion explicitly.

## Commands not run

This report does not claim:

```text
the complete repository pytest suite
the complete repository mypy suite
the repository-wide critical quality gate
hosted GitHub Actions at the exact implementation target
Lean, ESSO, Tau, SMT, or proof-system verification of B1B-1
```

Those broader gates are not needed to establish the narrow carrier-only
checkpoint. The exact-head reviewer may run additional bounded checks.

## Residual risk and non-claims

B1B-1 proves no deployment identity, migration legitimacy, current state,
configuration authority, publication atomicity, datastore linearizability,
governance authorization, content availability, crash recovery, or value
movement.

Python immutability remains a defensive API property rather than a language
security boundary. Every later authority-bearing phase must retain the
independent source at point of use and revalidate the exact carrier content.

No conclusion about B1B-2 follows from this implementation. B1B-2 remains
blocked until its source-bound pinned-migration design is separately approved
and a revised ATDD contract grants explicit implementation authority.

## Next safest step

Commit this report and the deterministic packet builder as the implementation
review target. Generate one documentation-only child packet containing the
exact target identity, complete changed-file inventory, source hashes, and
independent falsification prompt. Then obtain:

```text
APPROVE_B1B1_EXACT_HEAD_UNMOUNTED
```

before beginning B1B-2 implementation.
