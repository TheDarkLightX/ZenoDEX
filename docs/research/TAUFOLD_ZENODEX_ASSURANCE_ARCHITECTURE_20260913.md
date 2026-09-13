# TauFold assurance and ZenoDEX integration advice

Status: architecture guidance and isolated qualification work. No production
profile, balance migration, finality rule or publication authority is activated.

## Developer handoff

Start with this document and the [reviewed Python verifier patch](taufold_verifier_handoff_20260913/native-verifier.patch).
The [verification record](taufold_verifier_handoff_20260913/verification.json)
pins its public baseline, exact changed files, real verifier and evidence.
Review against the developer's current branch before applying; do not overwrite
concurrent work. This patch changes only the Python verifier boundary and its
tests. The backend interface below is architecture guidance, not an implemented
second proof system.

The candidate executes sealed, measured bytes; streams bounded child I/O;
strictly parses native responses; and preserves valid negative output `0`.
Claude Opus 5 implemented it. Astra integrated and independently reviewed it,
repairing empty-request and late-completion edge cases with retained regressions.
Final results: 27 focused tests, four real receipts and 49 rejection controls,
ten independent proof/context/executable controls, and nine independent
transport controls pass. Synthetic transport controls prove no computation.

On Linux with executable memfd/pidfd support, set `TAUFOLD_ROOT` to the matching
source checkout and `HANDOFF` to this document's `taufold_verifier_handoff_20260913`
directory. Set `VERIFIER`, `ORBIT_ROOT` and `ZENODEX_ROOT` to the intended
measured binary and host checkouts. Inspect the patch before applying it:

```bash
git -C "$TAUFOLD_ROOT" apply --check "$HANDOFF/native-verifier.patch"
git -C "$TAUFOLD_ROOT" apply "$HANDOFF/native-verifier.patch"
cd "$TAUFOLD_ROOT"
python3 -m unittest discover -s zkvm/tests -p 'test_native_verifier_*.py' -v
python3 "$HANDOFF/qualify_io.py" --source "$TAUFOLD_ROOT" --report transport.json
python3 "$HANDOFF/qualify_boundary.py" --source "$TAUFOLD_ROOT" --verifier "$VERIFIER" --host "$ZENODEX_ROOT" --report boundary.json
python3 zkvm/tests/adapters.py --verifier "$VERIFIER" --orbit-root "$ORBIT_ROOT" --zenodex-root "$ZENODEX_ROOT" --report adapters.json
```

The subprocess boundary assumes a trusted parent, kernel, loader and libraries,
responsive OS/filesystem, and exclusive child reaping: no SIGCHLD auto-reaping
or external `waitpid` handler. The pinned child must not escape its process
group. A sandbox prohibiting sealed execution must reject; use a qualified
execution environment rather than falling back to a mutable executable path.

## Exact subjects and useful reuse

ZenoDEX base: `4247e6194ac404e91429f3445654574cb4238d87`, on the V3 integration
branch. The next integrated obligation is versioned margin receipt/route
admission and an isolated current-store consumer. A small policy VM receipt
cannot replace that complete economic transition statement.

TauFold public source candidate: `55ec8821ccc6bf7ff95ab9726136764963513206`.
The [published source archive](https://thedarklightx.github.io/TauFoldzkVM/downloads/taufold-source.zip)
has SHA-256 `065a4fb34ed36cf0e3f2d2f97fc4b042f5f35cc71e5d78e3b3ec50acc4fdc259`.
Its VM and adapter contracts match the published release manifest. The dirty
local TauFold checkout is not the release identity and remains untouched.

Reuse the existing swap guard, exact invocation binding, immutable evidence,
and native cryptographic verifier. ZenoDEX already has a measured, sealed and
bounded receipt process boundary in `src/integration/global_receipt_verifier_v1.py`.
Do not add a competing process runner inside ZenoDEX. A TauFold endpoint must
adapt to that boundary or demonstrate why its required contract differs.

## Separate four responsibilities

```text
Tau machine semantics and application requirements
    -> deterministic program / checked execution relation
    -> backend-specific proof and independently selected verifier profile
    -> exact computation evidence
    -> ZenoDEX authorization, current-state admission and atomic publication
```

The prover proposes evidence. The verifier establishes execution under a pinned
relation. The application decides what that result permits. The publisher and
effect destinations enforce the approved transition. A proof of execution is
not a universal accounting or authorization theorem.

### 1. Stable semantics and versioned statements

Keep one small backend-independent description of the computation being proved:
semantic version and normalized Tau-source commitment, program commitment,
invocation commitment, input commitment, complete public result, executed step
count and outcome. Retain the existing ABI's other bound observables as well.
Reuse the current statement and canonical
bytes where sufficient. Do not introduce redundant commitments or change V1
bytes solely to create an abstraction. A material semantic change needs a
versioned successor and historical decoding.

Execution statements bind the program and outputs. A future economic statement
must additionally bind the exact pre/post state, command, effects and replay
identity through the established ZenoDEX ABI. Omission of those facts cannot be
repaired by giving a computation receipt an economic-sounding type name.

Keep VM bitvector arithmetic separate from checked financial arithmetic. The
current u32 VM wraps; its shipped guard avoids addition overflow. Wider token
amounts need an explicit checked representation, units, limits, rounding and
tests. Reject unsupported domains instead of silently narrowing or rescaling.

### 2. A narrow proof backend boundary

A conceptual interface is sufficient until another backend has a real consumer:

```text
verify(selected_profile, expected_statement, proof_bytes)
    -> verified_computation | typed_rejection
```

The selected profile owns the proof system and version, proof kind, verifier
artifact/key/image, statement codec, semantic relation, supported claim class,
resource ceilings and acceptance policy. Different backends have different
identities; their adapter must establish the mapping to the same semantic
statement. A shared digest alone does not prove that mapping.

The profile is independently selected by the host's admitted policy. Proof
metadata cannot nominate a verifier, key, guest, codec or development mode.
Unknown backends, unsupported claims, malformed proofs, exhausted limits and
verification failure reject. No automatic fallback after a rejected proof.
Capability descriptions are explanatory data, not authority supplied by a
backend or proof author.

Retain RISC Zero as the sole currently supported backend. Qualify its complete
invocation path through executable-snapshot, bounded-I/O, real-receipt and
context-substitution gates before enforced integration. Require equivalent
gates and exact-statement conformance for another backend.
Do not add a dynamic plugin loader, a generic proof registry or multiple prover
dependencies merely to reserve future flexibility.

### 3. Input provenance and business authorization

The current adapter binds a pre-state root and a private-input commitment. That
does not prove the private input is a value in that state. The integration must
obtain the commitment from an authenticated source with an explicit ownership,
asset, policy and epoch relation, or verify state membership/equivalent linkage
to an independently authenticated current pre-state with that same relation.
Opening the private-input commitment alone does not supply this linkage; the
current guest already checks that opening. An authenticated external report remains an external
premise rather than a theorem about physical holdings.

For the guard, proof validity and output `1` are separate predicates. Output
`0` is a correctly proved negative result. Keep both computation outcomes
available; the action admission gate must explicitly require approval.

Do not derive the expected context or input commitment from the submitted
bundle. A hash of an attacker-selected value authenticates no business fact.
Preserve the complete intent binding, including recipient, kind and amount.
Exact-out requests must retain the specified maximum-input interpretation.

Execution soundness and confidentiality have separate threat models. A cloud
prover can see private inputs entrusted to it. Public outputs, programs and
execution length can reveal information even when the witness is hidden from
the verifier. Retain the shipped programs' fixed-step behavior and qualify
privacy separately before accepting secrets into a remote proving workflow.

### 4. Atomic enforcement and lifecycle

ZenoDEX owns signatures, owner permissions, current policy/head selection,
nonce consumption, economics and atomic publication. Recheck the predecessor
and authority at commit, then commit complete state, receipt, replay record,
history and required outbox together. Exact retries and lost responses keep
their existing distinct contracts.

Ledger admission and withdrawal destinations must have no alternative
value-writing path that bypasses these checks. VM isolation does not secure a
compromised publisher/kernel with unrestricted balance or signing authority.
Independent validator and destination verification remains necessary for the
corresponding decentralized threat model. Finality adapter selection remains
separate from the economic transition and proof backend.

Historical proof verification, current profile activation/revocation and writer
authority have different lifetimes. Preserve old verification where required
without allowing a retired profile to authorize a new transition. Migration
and restored writer authority need their own gates.

## Assurance priorities for the TauFold developer

1. Close the measured-executable race and enforce streaming subprocess I/O
   limits. Execute exactly the immutable bytes that were approved; reject
   unsupported protection rather than executing a mutable path. Keep the OS,
   loader, libraries and verifier process as explicit trusted premises.
2. Keep the rejecting compiler small. Add independent translation validation
   or a correctness theorem for its accepted expression/transition fragment.
   Native/compiler parity is bounded evidence and shares possible specification
   mistakes. Include malformed, output-omission, arithmetic and branch mutants.
3. Qualify the existing private guard against real host intents and independently
   retained expectations. Add the authoritative state/input relationship before
   claiming an enforced spending budget.
4. Introduce a second backend only for a concrete security or performance need.
   Reuse statement and conformance tests, retain distinct backend identities,
   and measure prover cost, proof size, verification cost and legal-state fit.

An OR policy accepting any one proof inherits the weakness of any admitted
backend that can accept a false statement. An AND policy requiring independent
proofs of the same statement can tolerate one unsound backend if another is
sound, at additional cost and reduced availability. Shared semantic, compiler
and verifier-selection bugs remain common failure modes. A second backend is
therefore not an automatic assurance increase.

Cross-backend aggregation needs actual child-proof verification and exact
statement/ordering/context checks in the aggregate verifier. Hashing child
journals alone does not establish their validity. It is outside this first
integration and cannot earn ZRPF scaling credit without measured qualification.

## Acceptance and current nonclaims

The first isolated gate must replay a real guard receipt for the actual
ZenoDEX intent type, then reject changes to command/recipient, context, policy,
input commitment and proof output. Proved negative results must remain negative.
Transport controls must reject executable replacement, output flooding,
malformed responses and unavailable verification, while preserving genuine
receipt acceptance. Synthetic transport controls do not count as real proofs.

Next, an authenticated input relation and an actual current-store consumer must
demonstrate rejection with no economic/replay/outbox change and success through
the existing atomic publisher. Do not duplicate the publication machinery or
substitute this guard for the full margin/custody receipt.

This work supports W03 and the W06 verification boundary. It does not close
formal-core completeness, any economic lane or a production value-safety gate.
Percentage movement requires a separate review under the existing rubric.

Developer references: [VM contract](https://thedarklightx.github.io/TauFoldzkVM/source/CONTRACT.md),
[adapter contract](https://thedarklightx.github.io/TauFoldzkVM/source/adapter-contract.md),
[integration guide](https://thedarklightx.github.io/TauFoldzkVM/integrate.html).
