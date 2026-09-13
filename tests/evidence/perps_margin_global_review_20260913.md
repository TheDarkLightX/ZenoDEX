# Margin V2 joint successor: scoped review

Subject: `417ec94ad39389c8e2beceee69ceabe565828302`, based on
`2f1c0e0557edd5669413ead35bfaa2cd5773aac6`.
[Source pins, commands and nonclaims](perps_margin_global_v2_20260913.json).

Astra independently reviewed the Python architecture and exact production
sources. Two confirmed defects were repaired: unsupported consumed-object IDs
were accepted, and accepted-result getters retained mutable aliases. Direct
review probes and retained negative tests now establish exact rejection and
detached constructor/getter graphs. The reviewer replayed the connected
deposit/withdraw/transfer/refill/close history and independent nonflat oracle
and maintenance boundaries. Root inspected Luna's state and test implementation.

The successor preserves the existing economic kernel. Active account-to-claim
bindings carry information that owner/amount aggregates cannot recover. Draining
ends a claim while leaving the account open; refilling creates a fresh claim.
The asset lane's complete physical frame must change in the same candidate.
Supply and claimant liabilities remain distinct quantities. The existing V2
checker verifies the complete resulting economic tables, effects and replay.

The explicit snapshot/command/occurrence arguments are intentionally retained.
The constructor's seven fields bind the complete result to its refinement;
the transition's ordered rejection phases slightly exceed the length target.
Separate projection, economic decision and claim helpers keep those relations
visible without another context or adapter hierarchy. The complexity scanner's
parameter/length findings receive no automatic exemption from semantic review.

Astra implemented the episode model and finite bridge; root independently
reviewed their statements, premises, observation coverage and actual source.
The final source-bound gate passed three tests in 101.44 seconds, including
11 independently typed theorem consumers with standard-axiom checks, 115
Python/Lean complete-output cases and four output-corruption controls. Root
checked all final source hashes against the captured compiled sources. This
does not assert a separate second full compilation by root.

The model proves availability, exact active-account correspondence, sibling
framing, terminal-key retention, inactive-history immutability, last-positive
drain amount, fresh-only refill and existing V2 terminal-delta admission.
The same-owner two-account witness is constructive. Finite observation includes
every possible touched account/claim key; full actual helper outputs are compared.
The theorem assumes valid preprojection and an owner-preserving replacement.
It does not prove the Python interpreter, malformed-input equivalence, hashes,
resource completeness, global effects, authentication or publication.

Parent runtime evidence: 144 focused compatibility tests passed; the final four
new core test files passed 53 tests with 92.43% combined statement/branch coverage.
The broad critical gate passed 433 TCB tests and 852 critical tests; its coverage
targets are existing critical modules and do not substitute for the new tests.
Production-boundary checks passed while preserving unmounted/research status.
Actual 4,096-row balance exhaustion was tested; replay/terminal exhaustion used
deliberately lowered one/two-row limits. No 65,536-row rootability claim follows.

The independently reviewed narrow score amendment changes only margin deposit
and withdrawal: implementation .38→.50, semantics .50→.60, proof .45→.55,
refinement .45→.50. Uncertainty H, every other capability/workstream and all
qualification counts stay fixed. The calculator gives formal
**21.297%→21.419%** (+.122 points) and V3 **24.169%→24.239%** (+.070 points).
Judgment ranges are formal 15.589–27.505% and V3 16.983–32.317%. The bounds
reflect reviewer uncertainty, not statistical confidence or remaining effort.
No separate W09/global credit is added. The in-progress Rust twin receives none.

An earlier Opus architecture review informed the failure investigation; root
corrected its V1-only proposal against V2's actual lifecycle. A new nine-file
Opus source-review request was blocked before launch by automatic approval
review for payload-specific private disclosure; it produced no verdict. The
live Fable probe returned out-of-usage credits, and the Daybreak request hit the
native thread limit. Native Astra/root scrutiny and deterministic checks supply
this review; no nonexistent external review is counted.

Remaining scope: one margin market with the existing reserve-free asset frame,
Rust correspondence, canonical input decoding, authentic context/oracles,
versioned receipt and route admission, publication, recovery and deployment
qualification. Matching, funding, liquidation, insurance and whole-market
shutdown remain separate. No production authority or complete lane is claimed.
