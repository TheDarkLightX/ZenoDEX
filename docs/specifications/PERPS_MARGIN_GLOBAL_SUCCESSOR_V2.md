# Perps margin global successor V2

Status: pure Python/Rust implementation and isolated admission/store consumer;
receipt transport qualification uses protocol fixtures. Production authority `NONE`.
Baseline: `2f1c0e0557edd5669413ead35bfaa2cd5773aac6`.

This successor connects the existing deposit, withdrawal and account-close
economics to GlobalSettlementABI V2. It preserves the policies in
[the margin specification](../research/PERPS_MARGIN_GLOBAL_SETTLEMENT_SHADOW_V1.md)
and the [V2 compatibility contract](../research/GLOBAL_SETTLEMENT_ABI_V2_DELTA_AND_COMPATIBILITY_20260831.md).
It changes no V1 bytes, rounding, account limits or economic guard precedence.
It does not enable matching, funding, liquidation, insurance or market shutdown.

## Required connected behavior

Alice can deposit, partially withdraw, withdraw the remainder, transfer funds
to Bob through the existing asset lane, refill her still-open margin account,
withdraw again and explicitly close it. A closed account cannot reopen.
Two accounts owned by Alice can each have account nonce 1; the enclosing
occurrences use distinct subject replay nonces. The command body binds the
account nonce; it is not implicitly equal to the outer replay nonce.
This successor consumes no additional object IDs; a nonempty occurrence
`consumed_object_ids` tuple rejects as an unsupported command binding.

## State and claim ownership

The margin state owns its existing economic state and one active claim binding
for each account with positive collateral. Bindings are ordered by account ID,
have unique nonzero obligation IDs, and exactly cover funded accounts. Empty
open accounts and closed accounts have no active claim. A selected claim must
match the account owner, asset, `perps_margin` domain, PERPS_MARKET lane and
collateral amount. All OPEN perps claims must have an account binding.

An active binding is necessary information: the V2 terminal table does not
contain account IDs, and two accounts can have identical owners and balances.
The current account nonce cannot recover the occurrence that opened a claim.
Do not add a second journal, historical index or generation counter.

| Account collateral | Terminal transition |
| --- | --- |
| zero to positive | Create a fresh OPEN claim derived from V2 domain, release, market, asset, account and opening occurrence. Reject an existing ID. |
| positive to positive | Update the existing OPEN amount. |
| positive to zero | Mark the current claim DRAINED, retaining its final positive amount as required by V2; remove the active binding. |
| zero to zero on close | Retain all terminal history; close the economic account. |

Refill creates a new claim. It cannot reopen or overwrite a historical terminal
record. The global terminal table retains other lanes and drained history.
Per-account accounting locations equal collateral; per-owner liabilities equal
the sum of that owner's accounts. Physical holdings exclude claimant liabilities.

## Joint candidate and reuse

Inputs are complete immutable asset-custody, margin and global snapshots, an
exact typed command, a complete V2 occurrence and explicit optional oracle data.
The producer binds both input lane roots and release IDs to the global snapshot.
It checks collateral identity against the existing bound asset registry and
policy, including class, origin and eight-decimal units. Unsupported native
accounting rejects. The selected asset policy must be enabled.

The existing margin transition supplies the economic decision. Its V1 journal,
terminal projection and roots are not V2 evidence. The successor independently
constructs V2 effects, terminal plan and commitments. Existing shared V2
reconciliation checks the complete resulting candidate.

The asset-custody lane commits all physical balances and accounting locations.
The same pure step therefore reconstructs that existing frame and emits its
lane write whenever it changes, along with the PERPS_MARKET write. Both roots,
economic tables, liabilities, terminals and replay insertion belong to one
candidate. An unchanged asset root with changed physical tables is invalid.
The PERPS root itself contains only its owned state and claim bindings.

## Ordered outcome contract

1. Invalid Python value types or structurally invalid snapshots raise before
   any transition; they are outside the exact typed input domain.
2. Global occurrence context mismatch (chain, deployment, profile, predecessor,
   next height), then replay duplication, then V2 command-body/kind mismatch.
3. Complete lane/global projection or claim attribution mismatch.
4. Invalid registry origins, unknown collateral, disabled collateral,
   unsupported native accounting or incompatible collateral units.
5. Existing margin rejection precedence, including release, subject, market,
   account nonce, oracle, collateral and maintenance rules.
6. Insufficient external account balance; then global resource limits or
   failed exact successor reconciliation.

A typed rejection returns identical global roots, no successor, empty V2
effects and empty terminal/oracle plans. It changes no input, account nonce,
claim binding, replay row, history or outbox. An accepted result is a candidate,
not a verified publication witness. Supply, registry policy, history, outbox,
oracle state and unrelated economic rows remain unchanged.

`statement_root` commits the complete input. The shared refinement result
separately commits the output state, effects and terminal/oracle plans. Neither
value proves receipt validity, authentic oracle/command provenance or permission
to publish. Qualification here covers the joint asset and margin profile;
other lanes that commit shared tables need their own compatible frame updates.
The selected margin state represents one market. A registry of concurrent
markets and its complete projection are separate required integration work.
The reused asset-frame projection requires an empty global reserve table;
reserve-bearing profiles need a compatible complete physical projection.

Existing state/resource bounds apply. Terminal-table capacity blocks new claims,
not updates or drains of existing claims. Replay exhaustion blocks further
commands; balance-row exhaustion can block withdrawal to an absent balance row.
Guaranteed exits at those limits require a separately established capacity or
recovery policy. This contract does not silently reserve capacity or raise limits.

## Acceptance and remaining boundaries

Require the connected history above, same-owner equal-collateral accounts,
stale roots, wrong body/subject/origin, swapped or missing bindings, duplicate
replay, terminal reuse, repeated exact-no-op rejections and resource neighbors.
Use the existing ordinary-transfer consumer between margin steps. Retain the
V1 counterexample and golden checks; neither can be repaired by changing V1
terminal rules. A mutant retaining the old asset root must fail the history.

Constructor snapshots and immutable outputs protect retained aliases. The
episode theorem, finite Rust correspondence and isolated consumer below have
separate evidence. Universal runtime refinement, genuine receipts, migration
and production publication remain open. Historical V1 receipts cannot
substitute for the selected V2 guest. No live state migrates.

## Isolated receipt and joint-store consumer

The Python wire boundary owns a closed V2 request containing the command,
occurrence and explicit optional oracle. The isolated profile selects exactly
the asset and perps lanes, one market, an empty reserve table and initially
flat accounts. It admits deposit, withdrawal and close through the margin role;
ordinary asset commands retain the existing custody role. This consumer has no
position-changing route. Every supplied oracle candidate rejects before
signature or receipt I/O because its roots alone do not authenticate a price.
These restrictions do not complete the required open-position workflows.

The receipt journal is canonical JSON with exactly three fields:

```text
schema:          zenodex/perps-margin-global-statement/v2
input_root:      complete input statement_root from the joint transition
refinement_root: complete output/effect/terminal/oracle refinement root
```

Both coordinates are required. The input root alone cannot attest to the
selected successor. The new role pins distinct journal, receipt and
specification descriptors, the exact guest image and measured verifier bytes.
Its expected binding root is supplied by the independently selected
configuration. Evidence-status labels do not themselves qualify those bytes.
The shell copies caller values, checks the active profile and exact two-lane
route/releases, authenticates the command and occurrence, prepares the journal
and invokes the existing sealed verifier boundary. Economic rejection returns
before receipt acquisition. A verified journal grants no reusable write API.

The existing isolated SQLite publisher owns both roles and the complete
asset/margin/global predecessor. Its one commit closure rechecks the current
head and authority, then stores the economic replay frame, authenticated
message, signature and receipt with the new head in one transaction. Custody
steps carry the unchanged complete margin state; margin steps reconstruct both
lane states and the complete global successor. Recovery checks all three
predecessors against the retained history. Exact committed retries acknowledge
the old publication; a lost commit response remains indeterminate until retry
or recovery resolves it. A rejected attempt contributes no durable change.

The new framing is explicitly disjoint from historical custody deployment:

| Envelope | Contents |
| --- | --- |
| `ZDPM2` plus NUL | Four u32 little-endian length-prefixed canonical components: assets, margin, global predecessor, request. |
| `ZDJG2` plus NUL | Joint genesis: two independently bounded length-prefixed components, assets and margin. |
| `ZDJM2` plus NUL | Publication route tag 1 followed by a margin frame, or tag 0 followed by length-prefixed unchanged margin and the existing custody frame. |

Each canonical component is bounded by the existing 1 MiB decoder limit.
An economically accepted margin step whose asset, margin or global successor
exceeds that limit returns `SUCCESSOR_REJECTED` with the original root and
empty effects. Preparation and replay share this check: a committed successor
must remain representable as the next input. Existing custody frames already
decode their complete bounded successor. Publication count, history-byte and
replay limits still require a capacity/recovery policy for guaranteed exits.

The joint role root and publication/request identities have distinct domains.
Original custody-only frames and identities remain unchanged. Changing either
selected role or the expected genesis cannot silently restore writer authority
over an existing joint store. This is a fresh isolated deployment; it provides
no migration from a custody-only store and no live external effects.

Tests use real local SQLite transactions and signed-command checks with
protocol receipt fixtures. The selected Rust guest/image build and genuine V2
receipts are still required. Recovery currently trusts the retained store and
publication-time cryptographic result; an honest publisher, operating system,
configuration and storage remain premises. No external finality, rollback
anchor, delivery authority or production no-bypass claim follows.
