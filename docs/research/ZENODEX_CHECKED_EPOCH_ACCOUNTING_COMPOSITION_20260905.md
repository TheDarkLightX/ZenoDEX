# Checked epoch accounting composition

Implementation subject: `b972065ba0207592cde34f868a416ddbd778d061`, plus the
source-pinned proof and tests in this packet. This is a W09 accounting
composition obligation. It does not close W09 or the complete formal core.

## Statement and model boundary

Each route contributes rows keyed by all four coordinates:
`(kind, principal, asset, custody_domain)`. The composer visits routes in
command order and rows in their original order. It checks the signed bound
after every addition. Later cancellation cannot rescue an earlier overflow.

The new proof reuses the existing `GlobalState`, `EconomicEffectRow` and
`ExactEconomicTables` definitions. `TableChain` requires that every adjacent
pair of states and its route plan satisfy that exact table relation. A checked
composition then has, separately for every balance, custody, liability and
reserve key:

```text
composed_delta(key) = final_amount(key) - initial_amount(key)
```

The complete-key adapter preserves kind, principal, asset and accounting
domain. The proof derives endpoint accounting by telescoping adjacent table
differences. At every command boundary it recovers the actual accepted prefix
accumulator and the corresponding intermediate-state difference. It also
checks row prefixes inside an individual route, without regrouping them.

The success condition is exact: given the per-route table premise, a checked
result with those endpoint tables exists if and only if every relevant ordered
row prefix fits the supplied signed bounds. The arithmetic statement holds for
arbitrary finite lists. The runtime's separate one-to-64-command admission
limit remains a runtime obligation.

## Evidence and replay

The focused gate compiles the source closure with the pinned Lean toolchain in
temporary output directories. It checks independent consumer signatures and
axiom usage before accepting the theorem. Runtime comparisons and semantic
mutants are separate finite checks, not premises of the universal theorem.

Independent root replay passed all **9 tests in 57.97 seconds**. The packet
checks 20 independently stated theorem signatures and their axioms, 26 actual
Python composer histories and 129 Lean command-prefix observations. It also
checks the actual four-table runtime relation and two locally exact state
histories where every route and the endpoint pass their table checks but an
intermediate i128 sum rejects. The 64-command control succeeds; zero and 65
commands expose the separate runtime arity guard.

Three temporary model changes reverse command order, erase the accounting
domain or interchange custody and liability tables. Each causes a proof
compilation error. This is proof-failure mutation evidence; the gate does not
claim execution of those mutant runtimes.

```bash
python3 -B -m pytest -q tests/formal/test_lean_checked_epoch_economic_tables_v1.py
python3 -B -m experiments.v3_completion_followup_v1.render_evidence
```

The second command declares source and test hashes. It executes no proof or
test. Both checked-arithmetic modules are included by the default `Proofs`
aggregate so that subsequent full Lean builds include them. A full aggregate
build remains outside this focused replay.

Root review independently rebuilt the four-module source closure and compiled
a separately written endpoint-accounting consumer. The endpoint and ordered
prefix theorems use `propext` and `Quot.sound`; the positive example also uses
`Classical.choice`. No new axiom, `sorry`, `admit` or unsafe proof declaration
is present. The generic multi-language placeholder scanner mislabels four
solved Lean tactic placeholders as Agda holes because it searches every file
for any question mark. The Lean-specific scan, completed compilation and
actual axiom output provide the applicable checks; the generic scan is not
reported as passing.

The final proof SHA-256 is
`ee6ebc40358879e168cbc245be1641a06e084a39642d5da2736caacfa60897cd`;
the test SHA-256 is
`efd3cb46a8a4c952c994d74f3084971a36c61ef6bdbaf99305e723a373d05566`.
The complete source closure is pinned by
`tests/evidence/test_hygiene/THV1-20260905-checked-epoch-economic-tables-v1.json`.

## Remaining refinement obligations

The premise does not establish that each actual route verifier admits only
correct tables. Function-valued totals also leave the runtime's canonical
sorted, unique, zero-eliding tuple representation unproved. Universal
Python/Rust/compiler correspondence is still open.

The result covers four accounting tables. It does not establish supply
issuance/burning, conservation annotations, fee allocation policy, lane-write
authorization, replay, terminal state, Oracle finality, authentication,
receipts, publication, delivery or resource admission. Several commands sharing
one epoch are not modeled as separate height increments.

The positive four-table example witnesses the table premise and signed
composition. It does not satisfy full global admission: its physical balances
grow without a corresponding supply transition. Its claim is deliberately
limited to table arithmetic.

The next refinement step is to connect the proved complete-key totals to the
runtime's canonical output rows and to the actual per-route admission checks.
Neither this proof nor finite runtime agreement qualifies a release.

The subsequent [canonical-row theorem](ZENODEX_CANONICAL_EPOCH_ECONOMIC_ROWS_20260905.md)
closes the stated tuple-representation obligation in the Lean value model,
under explicit endpoint key uniqueness. Universal runtime execution and
per-route admission remain separate refinement obligations.
