# Retired Tau bridge evidence requalification V4

Status: successor contract; no acceptance until exact Stage A/B checks pass.
Scope: ordinary static Python import closure and existing finite route checks
for O-003B. Production, release, settlement and value-movement authority remain
`NONE`; zero value-movement gates close. No governance plan bytes or decisions
change. This is separate from proving immutable-state or economic correctness.

## Purpose

The historical result describes exact source bytes. Two owned-snapshot adapter
changes invalidate that binding even though their function bodies are unchanged.
Requalification must establish the same bounded claim for reviewed successor
bytes. Hashes identify the subject; replayed predicates justify the claim.

The preserved predecessor is V3 receipt commit
`abea06127ae3a6cd9aca38e18314673af7cd4ffb`, whose sole parent/source subject is
`ac468ec83f7a85b11e70508ee9d1e525f4f7ac2e`. Receipt SHA256:
`bd66f99523f904821e6417c588e41b96ef9a219f573d6cc4293d671a4c165dac`.
All V3 tools, receipt and historical tests remain unchanged. Historical V3
success is replayed from Git bytes and is never labelled current qualification.

## Successor contract

1. Acquire current committed and working bytes with the bounded, no-follow V3
   readers. Preserve exact subject ancestry, baseline, closed pin sets, path and
   size limits, source/blob checks, and current nonignored Python discovery.
2. Replay the predecessor's canonical artifact and derivation against its fixed
   Git subject. Require the preserved receipt bytes and original Stage-B topology.
3. Keep all legacy pinned bytes equal to the predecessor except five explicit
   reviewed SHA256 entries: two adapter files, the production-boundary checker,
   its tests, and its scope document. A pending or differing digest rejects.
4. For each adapter, allow only the named Snapshot additions to its existing
   state imports and the two copy-helper argument annotation unions. Compare the
   entire remaining syntax tree with its predecessor. This is a narrow syntactic
   comparison, not universal Python or transitive semantic equivalence.
5. Rerun every underlying V3 plan, route, import, discovery, dependency-row,
   classification and operation-registry predicate. Retain the fixed baseline,
   36 direct consumers, 92 current bridge import edges, zero added edges and the
   exact import classifications. The reviewed per-file delta replaces only the
   obsolete fixed current-source roots; all source roots are freshly derived
   and included in V4 evidence.
6. Pin the successor tools, contract and tests as extra committed sources. The
   receipt never pins itself. Its canonical bytes bind the complete bounded
   subject, predecessor, added pins, classifications and zero-authority ceiling.
7. Repeat source/discovery/receipt/HEAD/root-identity checks before acceptance.
   Require a quiescent single-writer checkout. Sequential checks detect observed
   drift; they do not provide an atomic filesystem snapshot.

The old V3 checker remains strict and continues refusing changed working bytes.
The production-boundary consumer selects V4 explicitly, checks the predecessor
identity and retains its no-authority checks. There is no fallback that converts
a stale V3 result into a passing successor result.

## Commit and replay sequence

Stage A commits only reviewed source, tests and qualification machinery. It must
not contain the V4 receipt. Preserve unrelated dirty work and review the staged
diff. Local commit permission does not authorize push or deployment.

```bash
python3 tools/build_retired_tau_bridge_closure_v4.py
```

Generation must succeed against that committed Stage-A source and unchanged
working bytes. Stage B has exactly one parent, Stage A, and adds only
`docs/research/ZENODEX_RETIRED_TAU_BRIDGE_CLOSURE_V4.json`. It must be a regular
non-executable Git blob. Modification of an earlier receipt is not accepted.

```bash
python3 tools/check_retired_tau_bridge_closure_v4.py
python3 tools/build_retired_tau_bridge_closure_v4.py --check
python3 tools/check_production_boundary.py --json
```

Descendant HEADs remain eligible only while the pinned Git entries, working
bytes and bounded discovery remain consistent. The qualified claim remains
attached to the Stage-A subject; it does not certify every descendant file.

## Acceptance evidence and nonclaims

Use ordinary metadata/representation conformance tests for canonical receipt
identity, exact added-receipt topology, preserved predecessor, allowed source
delta, terminal rechecks and strict rejection of invalid evidence. Independent
critical review must confirm guard preservation and the five reviewed digests.
Configuration-local test fixtures are not real Stage-A/Stage-B qualification.
The final gate must run on the actual committed subject.

Historical vulnerability reproductions, offensive workflows and broad mutation
campaigns are excluded. Historical V3 negative-test suites remain source-pinned
and are not rewritten to accept new working bytes. Any unrun evidence stays
explicitly unrun. The existing functional repair's 870-test result and its
remaining PerpsState gap remain separate facts. No whole-core, transaction
finality, custody, genuine-receipt, publisher, deployment or value-safety claim
follows from this certificate.
