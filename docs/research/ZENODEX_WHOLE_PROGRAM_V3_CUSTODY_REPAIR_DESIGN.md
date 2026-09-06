# ASSET custody-total repair: versioned implementation contract

Read-only review, 2026-09-05. No production code, fixture, proof, schema or policy was changed. The reviewed checkout advanced from `d02e2693476e597bbbb7cae75fb2905e004b0fff` to `45003d8d286fce4921a183bab148474f44c03f1d` while the parent committed the epoch-position extension; the exact relevant source hashes are below. Concurrent publisher/authentication changes are outside this semantic review.

The Opus note `OPUS_V3_CUSTODY_REPAIR.md` (SHA-256 `8d704419163eebe274e301eef7ca7409bbe5e74e7dfe145fb6d397b1b0773758`) is advisory input. This note independently reads the V1/V2 implementations and scalar consumers and corrects its evidence and versioning claims.

## Decision

Use a new ASSET module execution release with the existing V1 input, effect, private-port and journal formats. Preserve the old transfer leaf and old lane-wrapper/recomputation entry points. Implement the successor's completed conservation scalars at the wrapper, where the complete pre/post projection is already present. Existing `LaneModuleReleaseV1` metadata and content-derived release IDs can bind the new specification, source, toolchain and measured guest image; a new wire field or duplicated custody commitment is unnecessary.

The existing release records do not themselves select a Python/Rust transition implementation. New execution, recomputation and guest entry points must be wired together under a closed, reviewed release-to-semantics selection. The old admission path must remain available for its exact old subject. A caller-provided mode, function, effect total or claimed postcondition cannot select the new authority path.

## Exact accounting relation and frame

For each asset a, write Bpre(a) and Bpost(a) for physical account totals, Cpre(a) and Cpost(a) for physical custody totals, and S(a) for supply. The transfer leaf's existing row reports Bpre/Bpost. The lane projection and coordinator require Bpre+Cpre and Bpost+Cpost.

The wrapper supplies the same owned `module_input.custody` to both projections: Python [asset_transfer_lane_module_v1.py](../../src/core/asset_transfer_lane_module_v1.py), lines 264–286; Rust [asset_transfer_lane_module.rs](../../zk/global_settlement_abi_v1/src/asset_transfer_lane_module.rs), lines 173–201. Thus Cpre=Cpost is constructed by the wrapper before the additional W04 frame guard. It is not merely a downstream assumption. A future custody-mutating producer must use its distinct actual pre/post projections and establish its own effect/refinement contract.

For validated transfer input and accepted transfer execution:

```text
Bpre + Cpre = S = Bpost + Cpost
Cpre = Cpost
Bpre = Bpost
completed.pre  = exact pre_projection.owned_and_custodied_atoms(a)
completed.post = exact post_projection.owned_and_custodied_atoms(a)
```

No claimant liability or terminal obligation enters this physical sum. Global V1/V2 refinement includes physical reserves as well; the restricted ASSET publication relation separately requires reserves empty. A same-asset reserve or another lane's physical location cannot be silently omitted from a future broader global lift.

The existing V1 projection constructor requires balances plus custody to equal each u128 supply and rejects undeclared assets. Rust uses checked additions in both validation and `owned_and_custodied_atoms` (projection lines 103–161). Python sums exact integers and rejects any mismatch against the already bounded supply. Consequently a valid complete projection's resulting total cannot exceed u128. This is source reasoning about runtime guards, not a newly machine-checked universal arithmetic theorem.

The retained values 1, 7 and 2^127 are three concrete disagreement examples. They do not constitute exhaustive u128 coverage. The structural discrepancy B+C versus B holds algebraically for valid projections, under the stated complete-state and unchanged-custody premises.

## Minimal implementation sequence

1. Add a separately named custody-complete wrapper entry, for example `transition_asset_transfer_lane_module_custody_v1`, in new Python/Rust modules or an explicitly private shared wrapper implementation. Reuse the same exact V1 input and accepted value types. Preserve `transition_asset_transfer_v1` and `transition_asset_transfer_lane_module_v1` behavior and historical tests.
2. Snapshot and validate input using the existing complete boundary. Invoke the unchanged leaf once. Pass every leaf rejection through with its exact no-op result. On acceptance, construct the private pre/post projections from their actual states and the owned custody table.
3. Reuse the already implemented managed-asset pattern: Python `_complete_effects` and `_transition_owned_managed_asset_lifecycle_lane_module_v1` (managed wrapper lines 325–406), Rust `complete_effects` and its transition (lines 209–294). Replace only each affected row's two owned-and-custodied scalars with the corresponding projection total. Do not take the total from supply merely because validation says they agree; summing the authoritative physical rows keeps the computational relation explicit.
4. Rebuild all dependent commitments before constructing the accepted wrapper: completed effect-plan root, private port's module-effect root, base journal's effect root, private-port root, bound semantic receipt root and final journal. Preserve balance/custody/supply rows, movement/fee rows, issue/burn amounts, module pre/post roots, occurrence consumption and empty outbox/terminal fields. The existing wrapper receipt body is non-self-referential and can be reused.
5. Add the corresponding exact recomputation entry. Reuse existing structural policy/context binding and opaque-witness minting after deterministic equality. Existing V1 bind/verify entry points retain the legacy implementation; new release-aware entry points reject unknown or mismatched semantic families. A closed selection must bind the reviewed successor release specification and measured image through the existing authenticated profile/receipt boundary. No arbitrary callback or public boolean may relax old admission.
6. Mount only the new release at an isolated fresh initialization after the source/release/profile qualification exists. Carry its exact release ID through context/state, route module membership, coordinator compatibility and module receipt image checking. Preserve old state/profile decoding and historical proof subjects. Live migration of balances whose state roots bind old release IDs remains a separate authorized migration task.

Suggested edit surfaces for that implementation, after approval of the concrete packet:

| Surface | Required role |
|---|---|
| New `src/core/asset_transfer_lane_module_custody_v1.py` and Rust twin under `zk/global_settlement_abi_v1/src/` | New pure execution/recomputation; small shared private factoring only where needed |
| Existing lane wrapper modules | Keep legacy entry points; expose narrowly shared snapshot/port/journal construction if duplication would hide a binding |
| `lane_module_release_route_binding_v1.py` / Rust twin | New closed release-selected deterministic recomputation using existing policy and membership checks |
| `lane_module_receipt_verification_v1.py` / Rust twin | Select matching recomputation before exact image/journal verification; preserve opaque witness ownership |
| `zk/asset_transfer_module_risc0/shared/src/lib.rs` or a separately retained successor guest target | Statically select new execution semantics; retain canonical V1 input decode and bounds |
| `zk/asset_lane_coordinator_risc0/shared/src/lib.rs` | Recompute the same new module semantics and pin the actual newly measured module image |
| Route guest/profile qualification and `isolated_asset_receipt_pipeline_v1.py` | Use the same successor wrapper/admission and exact new child membership; requalify downstream proof context |
| New focused wrapper, relation, receipt and integration tests plus new golden fixture | Preserve all old expectations; add the new semantic contract independently |

The pure allocation consumer and certificate need no new total or claimant input. They already derive claimant continuity from the acquired predecessor, bind the accepted private projection and check exact allocation. Any source-closure or release-evidence updates must use their recorded generators after the new implementation is reviewed.

## Scalar consumer inventory

A repository search for both scalar names and direct attribute reads covered `src`, both ABI Rust crates, `tools`, and the existing Lean transfer files. The following are all distinct direct production scalar-reading behaviors found in those Python/Rust implementations; other producers and whole-plan copies carry the same fields through canonical effect roots.

| Consumer | Meaning / repair impact |
|---|---|
| V1 `AssetConservationRowV1` / Rust `effects.rs` | Check owned/supply change equals authorized issue minus burn, with exact u128 checks. Completing both transfer totals preserves these equations. |
| V1 `asset_lane_coordinator_v1.py:108–128` / Rust coordinator `:149–156` | Require exact absolute pre/post projection totals and supply, plus changed-asset coverage and exact physical deltas. This is the currently failing consumer and needs no relaxed guard. |
| V1 `global_economic_state_effect_refinement_v1.py:483–535` / Rust refinement `:565–591` | Compare effect totals with full physical balances + custody + reserves and full supply. The restricted empty-reserve relation makes the proposed completed scalar sufficient for this lane. |
| V1 `epoch_effect_composition_v1.py:68–108` / Rust composition `:108–161` | Require previous post totals equal next pre totals, preserve first/last totals and checked issue/burn accumulation. Test mixed legacy/corrected effects with custody: the old balances-only total must not silently splice into a completed sequence. |
| V1 managed-asset lane wrapper | Already completes both scalars from private pre/post projections and reconstructs dependent commitments. Reuse the pattern; do not change managed issuance/burn policy. |
| V2 `AssetConservationRowV2`, coordinator and global refinement / Rust twins | Distinct V2 state/codec family, described below. Do not change it incidentally. |
| V1/V2 canonical effect serialization and journals; V2 wire decoder | Preserve field names/order/width. Changed scalars affect effect roots and downstream journals even when physical rows do not change. V1 uses its own canonical effect serialization; the V2 codec cited by Opus is not the V1 runtime codec. |

`tools/check_asset_transfer_refinement_v1.py:477–480` and `zk/global_settlement_abi_v1/tests/asset_transfer_refinement_v1.rs:197–200` intentionally observe the inner leaf's account-only totals. Those oracles and the leaf theorem statements remain correct for their declared abstraction and must not be rewritten to expect wrapper custody totals. Add a new wrapper-to-projection theorem or test relation instead.

Other named producers, including managed lifecycle, perps and ZDEX effects, build their own conservation rows. Searches found no additional production direct scalar reader outside the categories above. This is a source-level inventory, not a claim that every deployed language/process/effect sink has been discovered.

## V2 distinction

`AssetTransferStateV2` has policies, balances and supplies and permits account total ≤ supply; its leaf reports account totals. `AssetLaneStateV2` has no custody field and enforces account total = supply at lines 244–254. The V2 coordinator checks the post leaf conservation total equals that aggregate supply at lines 153–170. Its normal aggregate route therefore operates within a complete account-only scope.

A V2 leaf alone can represent a supply/account gap, but there is no evidence here of a mounted V2 custody-carrying aggregate projection. Adding one would require a separate state/representation and ownership design. The V2 module/coordinator explicitly retain SHADOW/no-authority claims. Global V2's physical ownership function does include custody and reserves; that broader state does not automatically extend the narrower V2 lane. Preserve this as a coexistence/refinement limitation rather than applying the V1 wrapper repair to V2 by analogy.

## Release and historical evidence

`LaneModuleReleaseV1` already commits state schema, exact guest image, specification/source/toolchain roots, terminal/migration commitments and resource limits into its content-derived ID (types lines 432–529). A distinct semantic version string alone is insufficient: that descriptive field is absent from the release content-ID body, although it is serialized within the enclosing profile. The successor must have new substantive source/specification and measured-image bindings. Unchanged field layout permits retaining the V1 wire/schema roots when their documented meaning already includes custody.

The module guest calls the old wrapper directly. The coordinator guest separately recomputes that old wrapper and embeds the module image constant; the route guest invokes that coordinator preparation. All must agree on the successor before proof generation. New measured module images require fresh qualification even for zero-custody inputs. If the same input/context is used only for a pure computation comparison, adding zero should leave effect/journal bytes unchanged; that comparison does not transfer an old receipt to a new image or a new release/profile context.

Historical receipts remain cryptographically valid statements about their original image and exact journal. A repair does not invalidate them retroactively. They cannot supply authority for the new image/profile. Retain old image artifacts, canonical decoding, old semantic recomputation and their negative evidence. The current module witness API requires `ACTIVE_NEW`; raw historical receipt verification and new-transition witness minting have separate purposes. This review does not claim a complete mounted historical-admission service.

## Acceptance controls for implementation

| Obligation | Positive and negative controls |
|---|---|
| Legacy preservation | Existing V1 scalar/golden/refinement vectors remain unchanged. Retain the named 1/7/2^127 legacy coordinator disagreement test. Add successor positives rather than invert historical expectations. |
| Complete absolute totals | Independently sum physical account and custody rows for the command asset. Cases C=0,1,7,2^127 and several custody owners/domains; also other-asset custody that must not affect this row. Compare both Python/Rust outputs and resulting coordinator/global refinement. |
| Exact u128 boundary | Let B be a valid nonzero account total with a small admissible transfer. Choose C=(2^128−1)−B and both neighboring valid totals. Full projection and completed effects must accept at the maximum. Choose C one atom larger while keeping each row individually u128: complete input must reject before any partial success/receipt; preserve the exact typed Python/Rust boundary class. No fake out-of-range supply is used as an acceptance fixture. |
| Row growth / totality | 4096 canonical custody rows, last-row inclusion, and 4097 rejection before incomplete processing; duplicate/unsorted rows, foreign assets/domains and forged nonexact scalars reject. Keep allocated test state bounded and do not truncate. |
| Frame and authority | Pre/post custody tuples exactly equal input custody, including owner/domain/amount. Full claimant table, supply, issue/burn fields, fee policy and all unrelated assets remain unchanged. Test existing fee-owner alias classes, unauthorized sender, low balance, zero amount and base rejection no-op. |
| Commitment propagation | Independently check completed effect root equals port/journal roots, recompute receipt root and canonical journal, then use ordinary accepted snapshot validators. Omit exactly one rebind in a semantic mutant and require refusal. No opaque witness metadata is rewritten to manufacture a positive. |
| Exact allocation | Obtain each witness through the receipt verifier port. Prove/check nonzero custody with claimant partitions; conserved claimant reassignment, omission, duplicate-equivalent keys, extra terminal rows and wrong old predecessor must reject through existing guards. |
| Stateful composition | Build one and two accepted successor occurrences from an acquired source plus a chained prospective prefix. Check 1/2/8/9/64 supported positions with unchanged custody and exact replay. Mixed old/new totals, swapped evidence and disconnected pre/post roots refuse. |
| Release separation | New effects under old image/old release, old effects under new profile, zero-custody wrong-image receipt, foreign occurrence/context, unknown semantics and stale profile all refuse. Historical old-image cryptographic verification remains valid for the exact old journal. |
| Real proof qualification | After implementation and review, measure the new source-bound module image, rebuild/pin coordinator and route as needed, produce genuine zero/nonzero-custody controls under the common profile, and requalify changed root/epoch artifacts. No such proof was run in this review. |

For a new mathematical obligation, lift existing account conservation through identical external custody: derive Bpre+C=Bpost+C, exact physical projection totals and u128 representability from explicit validated-state bounds. The constructive `AssetTransferGlobalPreservationV1` theorem already separates physical ownership from claimant liabilities under representation/coverage premises; it is not a proof that the actual wrapper produces these effect scalars. An additional exact effect-row abstraction/refinement lemma is required. Universal Kani addition checks or a bounded actual projection harness may supplement this; three numeric tests never become a universal proof.

## Exact source manifest

| File | SHA-256 |
|---|---|
| `src/core/asset_transfer_module_v1.py` | `754d75a37ad70868bf20263fc189fc9e4f5a77cb864d8a1c7973afc253c938d7` |
| `src/core/asset_transfer_lane_module_v1.py` | `7c043b222d4e8aa3d54477ad7508ff65afd716f1b720f76f63995afc4daa7c1a` |
| `src/core/asset_lane_projection_v1.py` | `5420112e2dd321ce7f74604e66c13933ca714fc93467150f5cb6358f403b6839` |
| `src/core/asset_lane_coordinator_v1.py` | `6047468214d835ff9d6d9823d845df4ef0c4a1cd6d94f098911377daaf4996ae` |
| `src/core/managed_asset_lifecycle_lane_module_v1.py` | `312f6214901a46e912156c6b0f7c9f28008506f000abbae93aafb84b8587769c` |
| `src/core/global_settlement_types_v1.py` | `854a65b68a0c76a3af3afc62b53eb48c333b9e87f854e8f10fd54a851ff27ac4` |
| `src/core/epoch_effect_composition_v1.py` | `a678e459c3d57462c20fb787160c5e1ef9ed0706e62c293449b21a978efdd045` |
| `src/core/global_economic_state_effect_refinement_v1.py` | `abf60faacdcd45def5163e618494a2202c9c1ab7e11bde1f44b7b29cd0057697` |
| `src/core/lane_module_release_route_binding_v1.py` | `842897dea14ab65e3bccee6c13a44f4f56e6533a6daf3a0844f00372d3bf305c` |
| `src/core/lane_module_receipt_verification_v1.py` | `518ecd4a92593d7b7108e45787334e6c44201ef15510fc8e234e60aa30f92829` |
| `src/core/asset_transfer_module_v2.py` | `df0a25077d508db805afa0b828edbe5c8becdd362401f778fef0ce1f8649d065` |
| `src/core/asset_transfer_types_v2.py` | `ec067739d9da4a409347e8525c16188ecfcaad1e6b75172bfe1ca93e17cec40c` |
| `src/core/asset_lane_state_v2.py` | `650dc5ab0a2a6010b9b512bfc59bcb7a33e7d376bbffffdb106bda5abb65f5a2` |
| `src/core/asset_lane_coordinator_v2.py` | `be82d0ad5a7bc5ed49305a44711de9ca53a21f4ac7fc69fd1f232b33bc9462f8` |
| `src/core/global_economic_refinement_checks_v2.py` | `785643f2ecb7eb66d27b091ee04be0a186cab7c2746244fe4dada36627159d69` |
| `src/core/asset_transfer_global_allocation_v1.py` | `a4099cb3e53c26ef981e384e92cbdc5c04b80d5bdf7c14cd3b2d296a8830f028` |
| `tests/core/test_asset_transfer_epoch_allocation_v1.py` | `d7dc522f8321d083bd332557bb47890739e3013e05be6bbce0a92c68f5d4afd1` |
| `zk/global_settlement_abi_v1/src/asset_transfer.rs` | `78d28167d5360c22b3749812bdab224fe1a2b7888899db363b5dbc5d981dbcb0` |
| `zk/global_settlement_abi_v1/src/asset_transfer_lane_module.rs` | `26ac83d8359690a352328893debbf7d64685bd3bb44982527afcfbc4e4ce57a9` |
| `zk/global_settlement_abi_v1/src/asset_lane_projection.rs` | `c2c4aafd4ac7a4d23343e9e71fc1d36d59ee25de8476ed3a5c5bef9f55602c1c` |
| `zk/global_settlement_abi_v1/src/asset_lane_coordinator.rs` | `f4b8e0a1f79855136072168938df0c2003e830966b2e1e73b45fe3adebb5de5f` |
| `zk/global_settlement_abi_v1/src/managed_asset_lifecycle_lane_module.rs` | `bf55ace7af4801f13b7c622602ee7d99a0cef0558d9bd1e7104f1f5edfdc4d4a` |
| `zk/global_settlement_abi_v1/src/lane_module_release_route_binding.rs` | `ca656d0fcb505d58effeb00f5315e02b54d5ad63d892cb33afa1cb21f46361e6` |
| `zk/global_settlement_abi_v1/src/lane_module_receipt_verification.rs` | `e990844d670b474c5b8c2bb6c816dcbaa17fed2d7d7ea5944e7c509e1dd0b1c6` |
| `zk/global_settlement_abi_v1/src/effects.rs` | `0e691ba4be7be58ded9a87ba28f1cd747b67bf5cdfd4c39bbe232480fe20b7f6` |
| `zk/global_settlement_abi_v1/src/epoch_effect_composition.rs` | `8c66878bc29e4910537595a34edb5c81f707ae092e2a50345d43a082b48bbed6` |
| `zk/global_settlement_abi_v1/src/global_economic_state_effect_refinement.rs` | `e91f27cd2f38db434b1d8c77ef72a34508ec4ab744dff3843261fe263139316f` |
| `zk/global_settlement_abi_v2/src/asset_transfer.rs` | `a21aea1c2e642948edcdf7a0466b035bc26203572c5c22dc7185493e04077198` |
| `zk/global_settlement_abi_v2/src/asset_lane_coordinator.rs` | `05227226115f80748f8e340fb3a5a3b145072ab2e3d09688a7998e5221f6abca` |
| `zk/global_settlement_abi_v2/src/global_refinement_checks.rs` | `819520c05434d1eca6d0fffd98894fa56b42b7179ad7f70d3890719b7f6438de` |
| `zk/asset_transfer_module_risc0/shared/src/lib.rs` | `4c479de3d5f9f24b21364579ce359ba7654e0e5d7c6477c60814db18172923b5` |
| `zk/asset_lane_coordinator_risc0/shared/src/lib.rs` | `8d800bf2b9e9d73e705bd58937111ed4ec78284643c4d8d85d192b4e97da2ad5` |
| `zk/asset_transfer_route_composer_risc0/shared/src/lib.rs` | `0a242f0a22edb9faa9358919a06fec28e800a88deadb27a1a1978d76df1d7cf3` |
| `lean-mathlib/Proofs/AssetTransferGlobalPreservationV1.lean` | `350d22ed8796f9c847913f7b5a03f079ec33b484de1786fe3e95158c514aec7f` |
| `tools/check_asset_transfer_refinement_v1.py` | `6d219b570287a223105671db363d510a67390dbc51e3784045a2cd7abe33162d` |

Read commands used targeted `rg`, `sed`, `git rev-parse HEAD`, and SHA-256 calculation. No implementation, regression, arithmetic-proof or RISC0 command was executed as part of this read-only review. Previously retained passing tests are cited only as existing bounded evidence. The proposed repair remains unimplemented at this packet.

## September 6 follow-up: specification subject selection

The original review above remains historical. At integration subject
`5bc940e04a4f3cf29ea923fd8214cb8db9d3801a`, the pure custody wrapper and native
module/coordinator preparation exist, as recorded in
`ZENODEX_WHOLE_PROGRAM_V3_CUSTODY_WRAPPER_EVIDENCE.md` and the READMEs under
`zk/asset_transfer_custody_module_risc0` and
`zk/asset_lane_custody_coordinator_risc0`. They remain unmounted.

A follow-up source trace found no independent canonical specification subject
for selecting this successor in the inspected release definitions and custody
generators. `LaneModuleReleaseV1` and the Rust release type content-commit an
opaque `specification_root`. The Python/Rust release-route binders and receipt
verifiers still select legacy recomputation directly. The ordinal roots from
`tools/render_global_settlement_abi_v1_golden.py` are synthetic. Likewise,
`zk/asset_transfer_route_composer_risc0/build_isolated_fixture.py` labels its
release evidence as assumptions and reports `publication_qualified=false`.
Those fixture values cannot supply normative release selection.

The next implementation must define the independent specification bytes and
their canonical root derivation, then bind a closed combination of module,
coordinator and route semantic subjects to the corresponding execution family.
The fixed custody contract above supplies the account-plus-custody equation,
unchanged V1 wires, immutable custody and restricted empty-reserve condition.
The historical subject and its scope also need an explicit definition.
Unknown or mixed subjects must reject before recomputation or receipt work.
Semantic-version text, source hashes, synthetic fixture roots and caller
callbacks cannot select the family. Defining and reviewing these subjects is
remaining implementation work; no active release or live migration is created
by this source trace.

This follow-up is read-only evidence about the selection gap. It runs no
cryptographic qualification and makes no new safety or completeness claim.
