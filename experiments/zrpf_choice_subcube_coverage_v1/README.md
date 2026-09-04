# Named Choice-Fiber Subcube Coverage Experiment

Status: `BOUNDED_RESEARCH_ONLY`

Authority: `NONE`

## Question

Can a ZRPF aggregation guest certify that its child receipts cover every named
Boolean choice assignment exactly once, without enumerating all `2^n` complete
assignments?

The experiment uses a subcube represented by two bit masks:

```text
fixed_mask
positive_mask subset fixed_mask
```

A fixed zero bit has sign `-1`; a fixed one bit has sign `+1`. Unfixed choices
remain free.

## Two surviving checkers

### 1. Volume-Separation Partition Verifier

For arbitrary subcubes `C_1, ..., C_L`, verify:

```text
for every i != j:
  C_i and C_j fix at least one common choice to opposite signs

sum_i 2^(n - fixed_count(C_i)) = 2^n
```

The first condition proves pairwise disjointness. The second says the disjoint
union has the same finite cardinality as the whole Boolean cube. Together they
prove exact coverage.

Cost:

```text
O(L^2) pair checks under the bounded resource profile
O(L) volume terms
no 2^n assignment enumeration
```

Within the executable resource profile, this accepts every exact axis-aligned
subcube partition.

### 2. Canonical Named Choice Subcube Partition Tree

When the proof scheduler controls shard construction, require it to start with
the whole cube and repeatedly replace one region with both children obtained by
fixing one previously free named choice to `-1` and `+1`.

The complete binary tree makes overlap and omission locally impossible. The
canonicalizer chooses the least choice ordinal fixed by every descendant leaf.
Each leaf receipt binds the exact path-derived subcube, subject root, and opaque
proof commitment.

Cost:

```text
2L - 1 tree nodes for L leaves
O(L) structural checks and receipt hashes after reading the bounded manifest
O(L) encoded receipt-root commitments
```

This is the recommended ZRPF scheduling discipline. A recursive proof could
run the linear checker inside its guest and expose one succinct outer receipt.
The total guest work remains linear; recursion only makes host verification
succinct.

## Generality boundary

Recursive trees do not represent every exact subcube partition. Exhaustive
search found the smallest dimension where this matters: three choices.

The following five scopes exactly partition all eight assignments:

```text
fixed=011 values=000
fixed=101 values=001
fixed=110 values=110
fixed=111 values=010
fixed=111 values=101
```

Their sizes are `2 + 2 + 2 + 1 + 1 = 8`, and every pair is separated by an
oppositely fixed choice. No choice is fixed in all five scopes, so no recursive
split can be the root.

The brute oracle and volume-separation verifier accept this partition. The
tree constructor rejects it as `NON_RECURSIVE_SUBCUBE_PARTITION`.

The exact-cover search classified all small cases:

```text
n=1:   2 exact,   2 recursive, 0 nonrecursive
n=2:   8 exact,   8 recursive, 0 nonrecursive
n=3: 154 exact, 146 recursive, 8 nonrecursive
```

This is a deliberate scheduler restriction, not a mathematical equivalence.

## Bounded evidence

```text
10 focused unit tests passed
156 distinct recursively generated partitions checked through n=3
164 total exact partitions classified through n=3
8 nonrecursive exact partitions found, all at n=3
1,204 complete assignments replayed
5,922 brute membership probes
11/11 named attacks rejected
0 surviving named attacks
```

At 16 named choices and 256 leaves:

```text
tree verifier:       511 nodes, about 0.005 seconds
general verifier: 32,640 pairs, about 0.008 seconds
brute oracle:     65,536 assignments
                 16,777,216 membership probes
                 about 2.38 seconds
```

At 64 named choices and 256 leaves, the auxiliary coverage tree is 9,829
bytes and 511 nodes. The auxiliary explicit scope-list baseline is 16,499
bytes. Both measurements exclude the externally supplied receipt payloads.
The experiment does not enumerate `2^64` assignments.

The executable profile accepts at most 256 named choices, 4,096 receipts,
8,191 tree nodes, and depth 256. The brute-force oracle is separately capped
at 20 choices and 20,000,000 assignment-membership probes. These bounds turn
oversized inputs into typed rejections and keep recursive traversals below the
Python interpreter stack boundary.

Timings are single-host Python observations and are not performance claims.
Certificate sizes exclude cryptographic proof bytes.

## Killed attacks

```text
omitted branch
overlapping parent and children
swapped negative and positive children
choice-ordinal relabeling relative to an externally pinned manifest and subject
foreign promotion subject
altered proof commitment
surplus unconsumed receipt
alternate noncanonical split order
choice reuse on one path
general-checker omission
general-checker overlap
```

## Required ZRPF bindings

An implementation should include these values in the exact promotion subject
or aggregation journal:

```text
ordered choice-manifest root
choice-domain and correlation-semantics root
polynomial or transition-statement root
proof image and verifier-profile roots
pre-state / epoch / chain-continuity roots
canonical partition-tree root
ordered leaf-receipt aggregation root
combined output and economic-delta roots
```

Every child receipt must bind its exact subcube scope. The outer guest must
cryptographically verify child receipts before treating their commitments as
evidence.

## Disposition

```text
usefulness: high for controlled ZRPF shard coverage
novelty posture: utility construction; no novelty claim
production posture: unmounted research reference
```

Decision trees, subcube partitions, cardinality arguments, and recursive proof
aggregation all have substantial prior art. The useful result is the exact
integration contract among named choice identities, canonical shard scopes,
subject-bound receipts, and coverage checking.

## Nonclaims

This experiment does not establish:

```text
cryptographic child-receipt soundness
correct computation within any leaf
support for every possible exact subcube partition through the tree form
constant total proving work
ZRPF image identity or chain-continuity correctness
Tau Net throughput
production settlement authority
mathematical novelty or patentability
```

## Replay

```bash
cd experiments/zrpf_choice_subcube_coverage_v1
python3 -m unittest -v test_subcube_certificate.py
python3 run_experiment.py
python3 search_nonrecursive_partition.py
python3 -m ruff check *.py
python3 -m ruff format --check *.py
python3 -m mypy subcube_certificate.py run_experiment.py \
  search_nonrecursive_partition.py
```

## Files

```text
subcube_certificate.py             reference types and both checkers
run_experiment.py                  exhaustive campaign, attacks, benchmarks
search_nonrecursive_partition.py   exact-cover enumeration and boundary search
test_subcube_certificate.py        focused regression tests
README.md                          design, evidence, and nonclaims
```
