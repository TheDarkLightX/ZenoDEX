# FCIS M6 Luna Durable-Retraction Repair Report

**Contract:** `fcis-m6-durable-retraction-luna-repair-v1`  
**Date:** 2026-07-31  
**Posture:** `RESEARCH_ONLY_EXECUTABLE_UNMOUNTED`

## Exact source and topology

- Base commit: `babffa56dcbddc5886487fbb6e62740b15370000`
- Base tree: `eb6771943bc490d1f9664d26ec14622a8849b010`
- Repair branch: `agent/fcis-m6-r05-r11-durable-retraction-20260731`
- Prior packet head: `7deeb3403c933402393d15553cc87563aa71b752`
- Reviewed functional implementation target commit:
  `ecf26f987c3d6393501fec66ddfc3429fb8634c7`
- Reviewed functional implementation target tree:
  `fdf154ac143a9f9a9e840fbbf49761190d138920`
- Final packet: exactly one documentation-only child of the reviewed functional
  target. The hosted post-commit receipt records the packet commit, tree,
  parent, manifest digest, archive digest, and packet-file digests.

The functional target changes four files: the reference core, focused tests,
public finite-model checker, and read-only assurance workflow. The packet child
contains only research documents, task artifacts, exact repair inputs,
integrity records, and the canonical archive.

## Reviewed input hashes

| Artifact | SHA-256 |
| --- | --- |
| `fcis-m6-durable-retraction-tree.tar.gz` | `3d1ac7ed5d9404cc4b293a9707502e4e4d8d714498448501b4b878d7b8afcd70` |
| `fcis-m6-durable-retraction-bundle.zip` | `8e1c5cea2588682f84da2a9fe71f7e1b2bacd79143f1df12695d4542e81d9890` |
| `fcis-m6-durable-retraction-luna-repair-v1.zip` | `341ad62d45a3ff6cfa3b6437b482302654880f96c6c97e3fc505dd8db6c39a37` |
| `LUNA_PROMPT.md` | `acadf5085f77b640c6008f8321f280880e652e56fb22609cfbb0eef548efa94b` |
| `REVIEW_AND_REPAIR_SPEC.md` | `322f9de857b7ca073f40b280c2057cc69184622e06d547a82fa1ae8fe2f096b4` |
| `REPAIR_TASKS.json` | `373fb78412cfb8a74bfe90cd363e1b5e938c1930f00e8cdff5a557b69d36ed39` |

## Closed review findings

### Complete retry identity

`PublicationAtomV1.fingerprint` now commits `sequence`. A new atom is
`ABSENT_RETRYABLE` only when all of these hold:

```text
sequence = committed atom count + 1
authority epoch index = current authority epoch index
authority state root = current authority state root
expected pre-state root = current state root
writer profile is currently allowed
deployment and verifier profiles match the canonical history
```

Permanent witnesses reject same-content/different-sequence fingerprints,
sequence gaps, and stale or future authority-epoch indices.

### Verifier-at-use authority boundary

The module no longer contains importable construction tokens, caller-mintable
grant capabilities, or built-in accepting head/destination verifiers.
Authorization evidence and destination response evidence remain immutable
structural data. Every authority-bearing use freshly invokes a shell-selected
verifier and independently binds the result to the exact current subject.

The accepting adapters used by focused tests live only in the test module and
are named as test-only premises. A production shell must select and pin a sound
cryptographic adapter. This reference core neither supplies nor proves one.

### Public bounded-model gate

Public CI no longer checks out or executes private ESSO. The checked-in
`tools/check_fcis_durable_retraction_model.py` validates the exact ESSO-IR
subset, exhaustively explores every reachable state and enabled transition,
checks every invariant after every transition, and self-tests semantic mutants.

Current exact result:

```text
reachable states:     56
enabled transitions: 268
actions:              14
invariants:           10
mutants killed:        4
```

The retained private ESSO run is historical optional evidence. It is never a
required public workflow dependency or a substitute for production refinement.

## Exact local verification

The following gates passed against the reviewed functional target:

```text
python3 -m pytest -q tests/core/test_fcis_durable_retraction.py
44 passed

python3 -m ruff check \
  src/core/fcis_durable_retraction.py \
  tests/core/test_fcis_durable_retraction.py \
  tools/check_fcis_durable_retraction_model.py
PASS

python3 -m ruff format --check <same files>
PASS

python3 -m mypy --strict \
  src/core/fcis_durable_retraction.py \
  tools/check_fcis_durable_retraction_model.py
PASS

python3 tools/check_fcis_durable_retraction_model.py --self-test
PASS: 56 states, 268 transitions, four mutants killed
```

The Python bounded explorer regenerated the frozen result with 49 safe states,
254 safe transitions, and seven killed mutants. Julia 1.12.6 produced the same
structured result. The pinned `Proofs.FCISDurableRetraction` Lean target built
against mathlib commit `a3a10db0e9d66acbebf76c5e6a135066525ac900`.
The checked theorem file contains no `sorry`, user axiom, or unsafe declaration;
ordinary closure results retain Lean's recorded `propext` dependency.

Historical optional evidence records private ESSO commit
`ef5b06cb7dbed9e8a78d27e9918550ee591e42eb`, tree
`478db05f8f75f5c7cf0fe6164c097f0ea398cb32`, with 15/15 prior Z3/CVC5
inductive-query agreement. It was not rerun for this repair and is not needed
to reproduce the public packet.

## Luna task graph disposition

The 105-task graph remains a production implementation plan. All task records
remain `PLANNED` until their individual acceptance gates and receipts pass. The
current Python, Julia, Lean, and bounded-model results are prerequisite evidence
only. The continuation prompt pins this functional target and routes unavailable
private ESSO work to the public checker plus an explicit nonclaim.

## Nonclaims and residual obligations

- No concrete SQLite/PostgreSQL transaction, production CAS, WAL/crash
  refinement, or multi-process concurrency result exists.
- No production signer/quorum, deployment trust root, authenticated proof
  context, or destination idempotency adapter is supplied.
- No complete publisher inventory or mounted no-bypass result exists.
- No runtime mount, authority switch, migration, deployment, merge, or value
  movement was performed.
- No whole-system zUSD debt/backing theorem or production refinement is closed.
- A passing bounded model does not prove a production datastore or shell.

The next safe implementation slice is the concrete expected-root CAS and
canonical durable-layout adapter, followed by two-connection concurrency and
PRE/POST crash-recovery evidence. Keep the work unmounted until the production
shell, proof context, and no-bypass gates pass.

## Receipt-rebind repair addendum (2026-08-03)

The exact-head fields above describe the earlier PR #501 delivery. This
addendum is the authoritative record for the receipt-rebind repair slice.

- Prior packet head: `f36e1e301135b69a39f040e34c7de79a40054ff8`
- Implementation target commit: `91bce42607c2c2365087976bed1bee4a38cc1812`
- Implementation target tree: `d79465f3abc421838d6864368a57ac2ef48dc3ca`
- Implementation target parent: `f36e1e301135b69a39f040e34c7de79a40054ff8`
- Validator source SHA-256: `a3a328c9bb220a82b566e8683fa8aefe378b9083d5a7a9bab863ded9f33c320f`
- Packet-child parent: `91bce42607c2c2365087976bed1bee4a38cc1812`

The packet child records the strengthened Git-object lineage gate, report /
evidence identity bindings, the permanent zero-commit and foreign-tree
mutants, the ten public-text repairs, and the synchronized J07/J08/K06/K07
receipts. An external delivery receipt generated after the packet-child
commit records that child's exact commit/tree/parent, the deterministic
receipt archive digest, the branch, and every packet-file digest.

This repair remains `RESEARCH_ONLY_EXECUTABLE_UNMOUNTED`. It does not add a
production datastore adapter, runtime mount, authority switch, deployment,
merge, or value movement.

## Dependency-assurance rebind addendum (2026-08-04)

This addendum binds the current packet to the audited dependency repair:

- Prior packet head: `3c2a016e7ae702bddcca47831e15a5d17509010f`
- Implementation target commit: `2c3f21d87d49a31bceb1e74b19077bebcdb3cd2c`
- Implementation target tree: `16e6a2ee03e9e949431605c493c7ff9bc3aad5c7`
- Implementation target parent: `3c2a016e7ae702bddcca47831e15a5d17509010f`
- Hash-locked development requirements SHA-256:
  `f19d92eb044fdf0b23c50cba4a4d0054d5608579c0c04ab05d93a4a3880cc53e`

The implementation target raises the Python cryptography floor to `50.0.0`,
the MCP floor to `1.28.1`, and resolves the exact locks to cryptography
`50.0.0` and MCP `1.29.0`. The UI lock removes the retained npm advisories.
The four affected RISC0 locks use `ruint` `1.20.0` and `spin` `0.9.9`.

Local evidence includes an isolated `--require-hashes` installation with a
clean `pip check`, clean audits of all three Python locks, a clean UI audit,
the exact cargo-audit `0.22.1` RISC0 checker, compile checks for all four
patched RISC0 workspaces under Rust `1.90.0`, 61 focused dependency/profile
tests, 38 dependency-permission parser tests, and the UI contract, 86-test SDK,
configuration, lint, and production-build gates. The RISC0 checker continues
to expose its declared RSA and tracing-subscriber dispositions and
unmaintained-package warnings; this repair does not broaden those dispositions.

The packet remains `RESEARCH_ONLY_EXECUTABLE_UNMOUNTED`. Dependency repair and
source rebinding do not establish production durability, mounted no-bypass,
external destination behavior, or whole-system M6 closure.

## Sealed-evidence compatibility addendum (2026-08-04)

This addendum supersedes the preceding RISC0-lock posture for the current
packet target:

- Prior packet head: `4ff2122ebcc5ea848361dad23d7d587c304cac10`
- Implementation target commit: `9bc1a0f2bc271021432f690f3628e8cf58aa6996`
- Implementation target tree: `7e493180bf0c17185d71a926d4a6952e8ce955c2`
- Implementation target parent: `4ff2122ebcc5ea848361dad23d7d587c304cac10`
- RISC0 dependency policy SHA-256:
  `2913f714083b0ab1884282bf6401b6b9cfaf3b2b610301f1bb6bae2cc1433108`
- RustSec advisory database revision:
  `6d7aef354b4144c1ede046034adfd00246d3b0c0`

A pinned RISC0 force-build with the attempted `ruint 1.20.0` and `spin 0.9.9`
locks produced guest image identities different from the retained receipts.
Those locks therefore could not be presented as a dependency-only repair. The
current implementation target restores all four proof-bound lockfiles and
keeps every retained image ID, receipt, evidence inventory root, and proof
source inventory root unchanged.

`RUSTSEC-2026-0220` remains visible. Exact `risc0-binfmt 3.0.4` source review
found only ordinary ruint shifts with fixed 32-bit and 96-bit amounts and no
calls to the advisory's affected overflowing, checked, saturating, or wrapping
shift methods or `to_base_be`. The exact cargo-audit `0.22.1` gate accepts 12
scoped dispositions across four unmounted RISC0 workspaces and reports no
unused disposition. This is a bounded reachability disposition, not proof that
the dependency graph is safe. Removal requires new image IDs, fresh receipts,
and source-bound replay evidence under `ruint 1.20.0` or later.

The target also repairs two stale B1B CI assumptions. The ownership checker now
derives the exact pull-request merge base and validates only the closed B1B
subsystem surface, retaining every registered owner and forbidden path. The
workflow validates the immutable historical B1B packet by exact ancestry and
bytes rather than requiring the current head to be that historical packet
child. A closed source-only M6 state-binding chain is admitted as unmounted
research composition; any carrier or chain consumer outside the exact set is
rejected.

Local evidence at the implementation target includes 175 B1B Python tests,
nine Rust B1B parity tests, Rust formatting and clippy, the 1,011-file B1B
reachability scan, 42 RISC0 dependency/profile tests, the exact five-workspace
cargo-audit result, 740 ZRPF Python/evidence tests in the default sandbox, 19
sealed-verifier tests outside the sandbox's `/proc/self/fd` execution
restriction, and 16 clean-checkout source-closure tests. The ZRPF CBC report
still records five pending obligations and does not authorize production.

This packet remains `RESEARCH_ONLY_EXECUTABLE_UNMOUNTED`. It adds no runtime
mount, production datastore, publication authority, migration switch,
deployment, merge, or value movement.

## Lock-bound yanked-dependency addendum (2026-08-04)

This addendum is the authoritative dependency posture for the current packet:

- Prior packet head: `ee3618631c7a4266c05d15d9fdd3c8de6d1d600f`
- Implementation target commit:
  `92cc27f6315cbaa9c830066c41585a075f07857d`
- Implementation target tree:
  `4ee19c42470bd13cbe9ec2b2aef5ce0ad5a48c86`
- Implementation target parent:
  `ee3618631c7a4266c05d15d9fdd3c8de6d1d600f`
- RISC0 dependency policy SHA-256:
  `fd47e366052bcb149bdff1cb0688922e31b52130c1c2723d1b9a42a6ece188f1`
- Spin-only lock patch SHA-256:
  `139a13fbfe6dc34d10ef438693eb75d484475503be838aa5a1bcfee304cee7b4`
- Spin-only proof-identity comparison SHA-256:
  `aea09b01b4190a8c2d0a5db52b293a1a1e931dfc318964adf6dfcc178426607e`
- RustSec advisory database revision:
  `6d7aef354b4144c1ede046034adfd00246d3b0c0`

Hosted `cargo-audit 0.22.1` reported yanked `spin 0.9.8` in all four retained
proof workspaces. A local `--no-fetch` replay at the same RustSec database
revision omitted those yank warnings because cargo-audit obtains yank status
from the local crates.io index. The repaired checker does not treat the absent
local warning as proof that the package is not yanked. It applies the known
exception only when the committed lock contains exactly:

```text
package  = spin
version  = 0.9.8
source   = registry+https://github.com/rust-lang/crates.io-index
checksum = 6980e8d7511241f8acf4aebddbb1ff938df5eebe98691418c4468d0b72a96a67
```

The exact whole-workspace checker accepts 16 narrowly scoped dispositions: the
three prior vulnerability dispositions and one lock-bound yank disposition in
each of four unmounted proof workspaces. It reports no unused disposition.
Unknown, changed-version, changed-source, changed-checksum, or additional
yanked findings still reject. The crates.io index revision remains unpinned,
so hosted cargo-audit remains required to discover other or future yanks.
The public payload evaluator exposes no lock-authority parameter. Duplicate
cargo vulnerability or warning identities reject instead of being silently
collapsed.

The retained A/B experiment changed only `spin 0.9.8` to `0.9.9` in the four
proof-bound lockfiles and kept `ruint 1.19.0`. Under the pinned RISC0 toolchain,
all eight ZRPF guest ELF hashes and all eight image IDs changed. The exact lock
patch, baseline and trial lock hashes, guest hashes, image IDs, and toolchain
identities are source-bound in the comparison report. Guest binaries were
deleted after verification and no receipts were regenerated.

Local evidence includes 71 dependency-workflow and active-reproof tests, Ruff,
strict mypy, Python compilation, the active-reproof source-inventory checker,
the workflow-permission checker, the exact five-workspace cargo-audit replay,
and mutation tests for omitted/duplicated hosted yank warnings, direct
payload-only authorization, package source/checksum drift, and future unknown
yanks, plus duplicate warning and vulnerability identities.

This repair does not prove `spin 0.9.8` safe and does not authorize the yanked
dependency in production. Removal still requires `spin 0.9.9` or later, fresh
image IDs, fresh receipts, and source-bound replay evidence. The packet remains
`RESEARCH_ONLY_EXECUTABLE_UNMOUNTED` and adds no runtime mount, datastore,
publication authority, deployment, merge, or value movement.
