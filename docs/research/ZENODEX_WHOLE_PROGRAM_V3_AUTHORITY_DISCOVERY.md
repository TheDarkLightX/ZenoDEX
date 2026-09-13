# Whole-program V3 authority discovery

Research-only W00/W01 source review, 2026-09-04. This document records a bounded
static review, without deployment, proof generation, live activation, or gate
promotion. The reviewed source is immutable Git subject
`c6a9fd028ded9224427a645c1217d0ce576f78af`, parent
`beb43baaef629276f3dae07e8e62ebc42cc3217a`, tree
`4610bff736c26e436c43adb66de05f0a24ae20c7`. Later integration edits require their
own evidence. Reviewer: delegated Codex authority-discovery review; advisory.

## Result and subject reconciliation

The O-008 projection and durable publisher remain separate at this subject.
The ordinary node has a different publication path. A source inventory therefore
does not establish sole-writer mediation. W01 remains incomplete until the
selected deployment, dynamic targets, administrative paths and effect workers
are qualified together. No whole-program safety or product-completion percentage
is inferred from this review.

The normative floor is confirmed by parsing
`ZENODEX_M6_NORMATIVE_REQUIREMENTS_V1.json`: 103 lane capabilities, four required
routes and four exclusions. Its recorded status is
`RESEARCH_ONLY_STRUCTURAL_MAPPING_REQUIREMENTS_UNRESOLVED`. These are existing
artifact contents, not newly replayed closure results. The registry also records
20 unresolved policy rows; their individual present-day decisions must be
recovered before treating each as an unanswered user question.

Historical source-bound receipts remain useful routing aids:

| Receipt | Recorded subject | Recorded limit |
| --- | --- | --- |
| `ZENODEX_O007A_DEPLOYED_SINK_CLOSURE_V2.json` | `565e9b8e4b0e13392a1a6af8058d961199dd8846` | Static Python closure of 12 decoded repository launchers; records 54 unmediated writers and 26 closure gaps; no running deployment attestation. |
| `ZENODEX_O007B_CROSS_LANGUAGE_SINK_CLOSURE_V3.json` | `540916ff4489e9c0f6605562d07995fdda88298d` | Bounded AST/lexical operation inventory; no complete sink-syntax, generated-build provenance, or runtime-reachability theorem. |
| `ZENODEX_O007C_INDIRECT_SINK_CLOSURE_V1.json` | `2dd7cc5be29cc3a559d18a5de31f15f9842b6011` | Source dispositions; migration unmounted and committed-effect worker mount missing. |

All three receipts explicitly record zero closed value-movement gates. This
review does not refresh their source pins or promote their recorded counts to
current deployment facts.

## Authority and effect map

`IMPLEMENTED` means a reviewed source implementation exists. `UNMOUNTED` means
the intended launcher-to-capability path was not found in the reviewed static
surface and/or is explicitly disclaimed by its implementation. `GAP` names an
unclosed integration obligation. No `MOUNTED` or `PROVED` status is assigned here.

| Surface and source | Observed contract | Disposition and next obligation |
| --- | --- | --- |
| `bin/zenodex-public-testnet`, `bin/zenodex-local-testnet` -> `tools/zenoctl.py` | Shell launchers select the local/public testnet CLI. `zenoctl.py` dispatches `tools/zeno_ledger_node.py`; `.docker/entrypoint.sh` also starts `src.integration.api_server`. | IMPLEMENTED launcher paths; GAP exact release/deployment closure. Docker, operator, follower and installation roots remain in the O007A launcher union. |
| `tools/zeno_ledger_node.py::make_node_http_server_v0`, `append_dex_transaction_v0`, `append_dex_transactions_v0` | Node ingress and append shell; DEX candidate calculation uses `DexEngineConfig(require_intent_signatures=True, allow_unsigned_intents_if_tx_sender_matches=False, chain_id=...)` in the inspected tokenomics calculation paths. | IMPLEMENTED legacy ingress; GAP refinement to a selected `EconomicCommandOccurrenceV1`, active policy and unique epoch publisher. A signature flag is not an end-to-end authentication proof. |
| `src/integration/bls_intent_signing.py::sign_dex_intent_for_engine`, `sign_perp_op_for_engine`; `src/core/m6_authority_evidence_v1.py::verify_authenticated_execution_context_v1` | Signing and authenticated-context verification are distinct source surfaces. | IMPLEMENTED helpers; GAP release-bound signer/context/command/deployment/replay linkage for every mounted caller. Helpers do not grant publication authority. |
| `src/integration/dex_engine.py::apply_ops`, `src/integration/zeno_ledger_v0.py::apply_body_transactions_v0` | Existing operation execution and legacy ledger-body transition surface. | IMPLEMENTED; GAP all-lane canonical effect projection, finite-width refinement and global publisher consumption. |
| `tools/zeno_ledger_node.py::_build_faucet_block_from_body_v0`, `_build_tokenomics_reward_claim_block_from_body_v0`, `_build_autogovnext_block_from_body_v1` | These functions create state/header/body/checkpoint/receipt artifacts through node file writers. `_apply_tokenomics_buyback_burn_to_block_report_v0` updates the snapshot/header/checkpoint after its economic calculation. | IMPLEMENTED alternative writer families. GAP atomic complete publication and mechanical exclusion/mediation before production qualification. Multiple file writes are not evidence of one complete transactional publication. |
| `src/core/global_accounting_allocation_projection_v1.py::project_allocation_certificate_v1` | Pure allocation derivation over explicit state, roots and required witness slots; documentation honestly distinguishes invocation rejection, state ambiguity and checker acceptance. | IMPLEMENTED projection. UNMOUNTED at this source: no integration publisher consumer found. GAP authentic complete store snapshot, Rust twin and formal/runtime relation. |
| `src/integration/global_economic_durable_publisher_v1.py::VerifiedDurableEconomicPublisherV1.publish_economic_epoch` | Snapshots caller material, resolves a stored source head, checks selected profile/source, acquires a journal CAS token, invokes receipt verification, checks body/certificate binding and constructs the durable bundle internally. Constructor requires `RESEARCH_SHADOW` verifier selection. | IMPLEMENTED, explicitly UNMOUNTED research adapter. GAP allocation derivation from complete authenticated predecessor state and real receipt-verifier qualification. A stored root/head comparison is distinct from acquiring its full predecessor state. |
| `src/integration/global_economic_epoch_journal_v1.py::_commit_under_lock_v1` | `BEGIN IMMEDIATE`, validated current history, exact retry, current authority, expected source, bounded capacity, complete epoch bundle and current-head transaction. | IMPLEMENTED bounded CAS contract. GAP deployment sole-writer/process boundary, concrete datastore refinement and atomic migration retirement. |
| `src/integration/m6_commit_port_v1.py::M6CommitPortV1`, `src/integration/m6_durable_store_v1.py::M6DurableLedgerStoreV1` | Separate M6 reference/durable publication family for direct and ZRPF execution. | IMPLEMENTED parallel research publication family; GAP reviewed disposition or adaptation to the selected publisher. No equivalent wire/state contract is inferred from naming. |
| `src/integration/m6_outbox_delivery_v1.py::M6OutboxDeliveryPortV1.deliver` | Reads reopened committed M6 effects, binds durable attempt journal and genesis, reserves before transport, retains pending uncertainty after ambiguous transport. | IMPLEMENTED bounded shell on `M6DurableLedgerStoreV1`; UNMOUNTED committed-effect worker in retained O007C. GAP corresponding economic-epoch-store consumer, retained ancestry, destination idempotency, reconciliation and qualified finality. |
| `src/integration/global_economic_authority_journal_v1.py`, `global_economic_migration_journal_v1.py`, `global_economic_monotonic_anchor_v1.py` | Authority/recovery/migration/anchor surfaces are separate components with scoped contracts. | GAP authenticated restart authority and atomic successor activation/old-writer retirement. Existing authority documentation explicitly retains inode replacement, separate migration, and same-process private-writer limitations. |

In the pinned publisher, exact committed retry returns `ALREADY_COMMITTED` from
the journal before the current-authority check; it records historical success
without performing another economic commit. Ordinary stale-head/authority and
capacity outcomes carry no published epoch. Postcommit acknowledgment/anchor
uncertainty has a distinct exception. Preserve these distinctions when adding
allocation observation or admission.

The O007A manifest specifically retains dynamic/import/subprocess gaps in the
API, exact-out dispatch, perps loaders, Tau runner, receipt-verifier adapters and
operator tools, plus an oversized generated perps reference. O007C dispositions
do not prove those programs cannot write value. Revalidate selected targets and
writers under the actual deployment before closing W01/W11.

## Lane and route routing

The source entrypoints below route the next review; they do not establish
complete semantics for the listed lane. Common W06 publication and W09
refinement obligations apply to every row. Each current completion disposition
is `GAP`.

| Lane | Existing source/requirements routing | Specific unclosed obligations |
| --- | --- | --- |
| ASSET_TRANSFER | `asset_transfer_lane_module_v1.py`; normative WF-01; legacy `tau_testnet_dex_plugin.py::apply_app_tx` | Full capability family, registration/issuance/fee policy, authenticated context and store-continuous allocation; UP-13/16. |
| SPOT_LIQUIDITY | `dex_engine.py::apply_ops`; `batch_clearing.py`; WF-02/03 | Pool admission/closure, fee and LP rounding ownership, dust terminal disposition and authenticated routes; UP-12. |
| FARM_INCENTIVES | Normative lane capability rows and WF-17 global lifecycle coverage | Dedicated source/command-to-producer review remains UNKNOWN in this bounded pass; activation, emissions, cancellation and terminal drain; UP-03. |
| ZDEX_TOKENOMICS | Node tokenomics calculation/reward/burn functions; fee-allocation and burn module families | Governed designated fee source, same-occurrence Spot purchase/exact burn, retained-supply policy, hosting/staking claims; UP-01/02/14/15. |
| ZUSD_MONETARY | `zusd_monetary_bridge.py::apply_zusd_monetary_ops`; WF-04..09 | Monetary issuance/burn ownership, collateral/liquidation/recovery policy and shared-asset release coexistence; UP-04/17. |
| PERPS_MARKET | `perp_engine.py::apply_perp_ops`; WF-09/10 | Funding, margins, insurance priority, ADL/bankruptcy and terminal closeout; UP-05/17. |
| ORACLE_MARKET | Legacy Tau multiplex and zUSD bridge; WF-12 | Authenticated occurrence/finality, query/bond/reward/dispute/clawback and terminal policy; UP-06. |
| SEALED_AUCTION | `confidential_sealed_bid_api.py::ConfidentialSealedBidTable.commit/settle`; WF-18 | Bond custody, reveal/expiry/cancel/refund/slash, inventory and winner authorization; UP-07. |
| STRATEGY_ESCROW | Normative lane and route rows | Dedicated source/command-to-producer review remains UNKNOWN in this bounded pass; trigger, replacement, expiry, recovery and route authority; UP-08. |
| PROOF_REWARDS | `proof_mining_runtime.py::apply_proof_mining_claim`; WF-11 | Funding ancestry, claimant eligibility, nullifier scope, payout and task terminal disposition; UP-09. |
| EXTERNAL_CUSTODY | `zeno_ledger_cross_shard_effect_application.py` state/balance/terminal effect functions; M6 delivery port; WF-14/15 | Origin/destination registration, authentic finality, delivery/recovery ancestry and destination idempotency; UP-11. Starts empty; unregistered destinations reject. |
| GOVERNANCE_MIGRATION | Node governance admission writer, governance session store, migration/authority journals; WF-13/17 | Command-only governance authority, policy epochs, concurrent writer retirement and migration continuity; UP-10/16. |

| Required route ID | Lane composition | Required exit evidence |
| --- | --- | --- |
| `fee_funded_zdex_purchase_and_burn` | SPOT_LIQUIDITY + ZDEX_TOKENOMICS | Designated fee spend and exact received ZDEX burn from the same occurrence; no treasury-burn substitution. |
| `zusd_liquidation_settlement` | ZUSD_MONETARY + relevant settlement/oracle owners | Exact collateral/debt/supply/liability result, authorized Oracle occurrence and atomic terminal disposition. |
| `perps_epoch_settlement` | PERPS_MARKET + settlement/oracle owners | Ordered epoch funding/settlement, margin/insurance/ADL ownership and all-or-nothing publication. |
| `strategy_triggered_spot_swap` | STRATEGY_ESCROW + SPOT_LIQUIDITY | Authorized trigger, escrow consumption/recovery, exact route pairing and atomic outcome. |

The four exclusion IDs remain `zusd_emergency_shutdown`,
`unregistered_external_destination`,
`autonomous_governance_publication_authority`, and
`caller_selected_route_or_proof_profile`. A disabled required capability is
still incomplete. The explicit day-one emergency-shutdown exclusion requires
no-writer evidence, while cancellation/recovery obligations for enabled paths
remain required.

## Prioritized W02/W06 contract decisions

1. **Outcome conflict requiring explicit successor semantics.** The retained
   normative WF-01/BDD-003, WF-02/BDD-006, WF-03/BDD-010 and WF-05/BDD-019 describe
   some business failures consuming ingress nonce/history. The existing M6
   publication family explicitly supports `BusinessStatusV1.REJECTED_COMMITTED`
   (`m6_commit_port_v1.py`, `M6PublishedRecordV1.__post_init__`). V3 requires
   precommit rejection to contribute no economic/replay/history/outbox change.
   Preserve historical verification and declare whether such prior committed
   failure records remain historical-only or are a distinct admitted command
   outcome. Do not silently relabel them as pure rejection or regenerate the
   old registry to erase the difference.
2. **Projection information and source ownership.** Derive every available
   allocation field from authenticated committed state and pinned ownership
   policy. The current projection documents that receipt root and required
   witness data are not all recoverable from V1 state alone. Snapshot capture
   must bind complete state and authentic predecessor; a core parameter ban or
   receipt-shaped caller object cannot establish provenance. Determine journal
   sufficiency before any versioned field addition.
3. **Publication and observation boundary.** SHADOW consumes committed snapshots
   through a read-only interface. Diagnostics have bounded separate storage and
   never enter economic roots or admission. Observation absence/failure is an
   evidence gap. The publisher revalidates current head and current authority
   at its linearization point; the subprocess verifier has no publish handle.
4. **Reuse decisions before policy interviews.** V2's UP rows are routing
   anchors, not proof that every current setting is unanswered. First recover
   the selected release/policy documents and record per-parameter provenance.
   Priority shared blockers are fee allocation/retained supply, zUSD shared
   asset coexistence, external finality, accounting scales, authority/replay/time
   domains and terminal owners. Local-testnet constants are not policy approval.
5. **Historical identity and migration.** Keep immutable release identity,
   active policy epoch and publication identity distinct. Migration requires
   atomic successor activation plus exclusion of old writers; a separate
   migration journal does not establish this. Do not activate live authority or
   migrate balances during isolated qualification.

## SEC candidate review and integration disposition

Exact candidate: `b802c942a8c7ccf8bf17b1b61021cbd8c960b7ea`, parent
`32e27d438a6149d5d2c0d971f61ee7f260000d76`, tree
`63ef49159741a1ff4ef250ad7ad35966f185ad14`. Review used only that commit's delta
and the immediately relevant candidate files. It changes seven files: two
documents, API server, a new secret-field guard and three test files. No
projection, publisher, receipt cryptography or ledger allocation code changes.

Disposition: **REVIEWED_STATIC, INTEGRATION_PENDING_CHANGES**.

- The new pure guard rejects a fixed normalized field-name vocabulary in decoded
  objects and queries, with iterative bounded traversal and stable refusal codes.
  This is useful input-schema defense. Candidate tests cover vocabulary/parity,
  decoded spelling, nesting and mounted handler refusal; those tests were read,
  not executed in this review.
- Claims that this prevents the server from having access to key material exceed
  the implementation. The server already reads and decodes body bytes before
  rejecting recognized field names. Values under other names are not inspected;
  upstream request/query logging is outside the guard. State its narrower
  refusal contract and audit logging/key flows separately. This is a technical
  scope finding, not a legal conclusion.
- `_secret_material_refusal_for_body` adds `json.loads` before dispatch and only
  catches `JSONDecodeError` and `UnicodeDecodeError`. Parser resource/depth failure
  handling needs an explicit bounded rejection contract for this new chokepoint.
  No hostile input or network reproduction was run.
- `CUSTODY_TERMINOLOGY.md` recommends renaming `custody_domain` to
  `control_domain` and says this changes no behavior. On the O-008 branch this
  field participates in canonical serialization/root contracts. Any rename
  requires an explicit version/pin/regeneration/migration decision; V3 preserves
  existing wire formats absent a reviewed semantic successor.
- Date-sensitive legal source/status claims were not verified. They require
  primary-source review before adopting those document assertions. This report
  grants no legal clearance.
- A read-only `git show --format= b802c942 | git apply --check -` against the
  clean integration subject failed at API-server and request-grammar-test
  contexts. The patch cannot be applied unchanged. Its historical path
  fingerprint must not be copied as O-008 evidence.

## Source pins and verification record

The exact Git subject above binds every reviewed file. Useful independent blob
identities for replay are:

| Path | Git blob |
| --- | --- |
| `tools/zeno_ledger_node.py` | `e745a2a7e6aa8cd3bd5027a7fbb1a4b1b5a7347f` |
| `src/integration/zeno_ledger_v0.py` | `d31b64391c6c5d7764cfa4dd2cb994023d5826a6` |
| `src/integration/global_economic_durable_publisher_v1.py` | `145dffd647490b8b60952dab4b2676c2d1c06a97` |
| `src/integration/global_economic_epoch_journal_v1.py` | `e806056420e9e06e848dfba02c7f7ade45ac4ad0` |
| `src/integration/m6_outbox_delivery_v1.py` | `5025994855e67ed19a2bf2f9677dd0f15761579e` |
| `src/core/global_accounting_allocation_projection_v1.py` | `d64b8691a61c3e45a4700a0fb4c53a0248b0dd36` |

Performed: source/status/hash inspection; JSON requirement/manifest parsing;
exact SEC commit/parent diff review; source-function AST enumeration; read-only
patch applicability check; repository style classifier for this document. The
classifier selected public-claim evidence discipline. Root and documentation
overlays were read. The root-referenced `phase2_workspace_diff.md` was absent at
the inspected root; no substitute instructions were invented.

Not run: receipt verification, unit/integration suites, mutation campaigns,
Lean/ESSO/Kani/RISC0 builds, scanners over the full repository, current closure
receipt regeneration, deployment reachability, live operations, remote jobs or
legal research. These are deliberate scope limits of this read-only review.

The original September analysis and A+ plan were recovered by following the
agent-prompt index's provenance outside the plan-analysis checkout. Exact
recovered bytes:

| Recovered artifact | SHA-256 |
| --- | --- |
| Whole-plan architecture analysis, basename `zenodex-formal-core-plan-analysis-20260903.md` | `f01730253a7d6570c43a629ce72cc025d6bb17fd0881a90e35e980eeae46616f` |
| A+ superseding execution plan, basename `zenodex-formal-core-plan-a-plus-20260903.md`, version `A+/v2` | `fd8c0fcabd2be7f4555c47a350162f3ab4c5b9794dac5c2a2f67b55128c74f65` |

The exact G1-G14 identifiers and severity labels below come from analysis
section 3. The finding column summarizes its historical claim. Original line
numbers refer to the recovered 571-line analysis. `OPEN` below means the
corresponding completion obligation remains open; it does not assert every
historical implementation detail still holds.

| ID | Severity | Original line | Historical finding | V3 owner and present review disposition |
| --- | --- | --- | --- | --- |
| G1 | S1 | 92 | Python receipt-verifier port has no cryptographic plug; test verifiers mint the witnesses. | W03/W10: OPEN real verifier and exact real-receipt qualification. Existing Rust receipt verification is a separate surface. |
| G2 | S1 | 114 | Allocation certificate has no consumer; epoch verifier has no non-test caller. | W05/W06/W11: UNMOUNTED at reviewed base; publisher has no allocation-projection consumer. |
| G3 | S2 | 130 | For the current profile, the certificate is a pure function of verified post-state; twelve witness slots add no information. | W02/W04: SCOPED_REQUIRES_QUALIFICATION. Reuse the named one-lane liabilities decision; current projection still requires receipt/witness inputs, and V1 sufficiency is not universal. |
| G4 | S2 | 149 | Chain continuity is caller-asserted. | W04/W06: OPEN complete store-acquired predecessor/allocation binding. Existing stored-head and CAS checks are implemented and must be retained. |
| G5 | S2 | 161 | Guest image IDs and release selection are asserted rather than measured. | W03/W10/W12: OPEN exact rebuilt-image, verifier-binary and selected-release evidence. |
| G6 | S2 | 174 | Eleven lanes lack producers; epoch path supports only single-lane ASSET_TRANSFER routes. | W07/W08/W09: OPEN all required capability/lane/route closure. Disabled required lanes cannot count as complete. |
| G7 | S3 | 185 | Mutation ledger is a string claim that no gate executes. | W00/W09/W12: HISTORICAL_REPORTED_IMPLEMENTED by A+ P0-2; execution on the exact release remains required. This review did not replay the mutation engine. |
| G8 | S3 | 197 | Exact-type discipline addresses an excluded hostile-process adversary and its pin is syntactic. | W09/W11: SCOPED_TRUST_BOUNDARY. Exact owned values aid accidental-boundary safety; process/OS compromise protection is not established by Python type checks. |
| G9 | S3 | 207 | Model-to-code bridges compare names. | W09: OPEN semantic runtime/refinement relation. Name/source/hash/parity agreement alone cannot close it. |
| G10 | S3 | 219 | Certificate integer bridge is replayed, not proved. | W04/W09: OPEN bounded actual-Rust arithmetic/totality and formal/runtime bridge; no Kani/Lean execution occurred in this review. |
| G11 | S3 | 228 | Receipt kind is a caller-selected tag. | W03/W10: OPEN receipt-byte cryptographic-kind enforcement; enum/tag checks alone are insufficient. |
| G12 | S4 | 235 | Pinned battery/chain scripts fail open. | W00/W12: HISTORICAL_REPORTED_REPAIRED. A+ review appendix records this closed at its own tip; preserve failing-tool controls and replay before current release claims. |
| G13 | S4 | 242 | Epoch path retains thirteen `isinstance` sites. | W00/W09: HISTORICAL_COUNT_NOT_REPLAYED here; qualify needed owned-value reconstruction under the declared trust model, without treating a syntax count as proof. |
| G14 | S4 | 248 | PopperPad has no `formal-core` knowledge. | W00/W09: HISTORICAL_EXTERNAL_STATE_NOT_REFRESHED. Preserve discovered negative results; knowledge recording grants no economic authority. |

Neither the original G12 finding nor the old D+ grade is a current verdict.

The A+ accepted decisions also provide policy reuse: the V1 liabilities
partition is authoritative for its named one-lane profile, subject to its
totality/ownership conditions; deterministic projection replaces redundant
consumer witness slots while retaining internal admission witnesses; the
pinned subprocess verifier comes first; full proof generation stays remote.
Those accepted decisions do not establish the semantics of additional lanes.
V3's explicit corrections control observation isolation, purity, journal
sufficiency, identities, complete scope and production sequencing. The
September 2 Claude Tau ADT/C9a plans are separate historical work and were not
substituted for these recovered originals.

| A+ decision or architecture element | V3 disposition |
| --- | --- |
| Named one-lane V1 liabilities partition is authoritative, subject to totality/ownership conditions. | INHERIT for that exact restricted profile; additional lanes require their own policies and ownership relation. |
| Deterministic projection replaces redundant consumer witness slots; existing admission witnesses and negative evidence remain. | INHERIT the design direction; establish information sufficiency and runtime refinement before retiring interfaces. |
| Measured subprocess verifier comes first and cannot reach the store. | INHERIT W03; context/allocation/current-authority checks remain separate obligations. |
| No full local proof generation. | INHERIT; remote expenditure remains separately scoped. User later authorized careful inventoried cache cleanup only. |
| Keep Tau PR #534 draft pending exact-pin/lineage qualification, with conflicting prior work orders recorded. | RETAIN as a separate unresolved Tau integration qualification; no production capability is inferred or promoted here. |
| P1 provenance enforcement through parameter/AST restrictions. | SUPERSEDE: pure core accepts explicit immutable authenticated snapshots acquired by the shell; syntax cannot prove provenance. |
| P2 profile mode and publisher-coupled SHADOW recording. | SUPERSEDE: read-only committed observation with bounded separate diagnostics and no economic/profile-root effect. |
| Byte-identical store checks for every rejected case. | SUPERSEDE with logical no-effect rejection; concurrent winners and database housekeeping may change physical bytes. |
| Journal extension by an allocation-fragment field. | SUPERSEDE any presumption of necessity: first prove whether authenticated state plus pinned ownership policy determines the allocation. Extend only genuinely missing information in a reviewed version. |
| CAS-ticket, verifier, context, authority and outbox ladder. | INHERIT the qualified logical dependency; ticket freshness alone is not publication authority. Preserve exact retry and postcommit uncertainty distinctions. |
| Release/profile/publication identity and profile-root migration question. | REFINE with separate lifetimes and historical decoding; observational modes do not change economic profiles. New active policy still requires authorized migration/activation rules. |
| Restricted one-lane campaign ending at SHADOW. | SUPERSEDE completion ceiling: SHADOW is an intermediate observational milestone; all twelve lanes, four routes, concrete shell, release and product obligations remain required. |

The recovered originals were only read and hashed. No source, historical plan,
receipt, or original analysis was removed or rewritten during this review.

Next concrete work: qualify complete read-only committed snapshot acquisition
and observational isolation; then connect independently qualified receipt
verification and allocation admission to the isolated publication transaction.
Production promotion remains closed while any discovery, policy, refinement,
writer, migration or effect-delivery obligation above remains open.

## September 13: isolated margin qualification CLI

`tools/qualify_margin_receipts_v2.py` adds a development-only caller of the
existing `IsolatedCustodyPublisherV2`. `prepare` authenticates public test
commands and exports frozen inputs without creating a store. `publish` creates
a fresh isolated database and submits returned receipt bytes through the same
signed-command, selected-verifier and atomic publication checks. It accepts
neither remote configuration nor remote post-state. Existing databases are
refused by the publisher's exclusive-create boundary. The custody-transfer role
and economic release labels remain fixture assumptions; the tool exercises only
the margin role and has no production launcher or external-effect mount.

This is source classification of the new caller, not refreshed deployment-wide
writer closure. Genuine receipt publication is pending; AS01/AS03 and the
honest publisher/OS/genesis premises remain open.
