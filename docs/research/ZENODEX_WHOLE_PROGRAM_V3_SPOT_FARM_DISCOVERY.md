# V3 SPOT and FARM semantic discovery

Date: 2026-09-05. Subject: `2507a99f0f3dd4811dc12114a421c1ad1bc7cf73`, plus the separately hashed new signature-purpose test. Status: bounded W02/W07 discovery and advisory review. No policy values, source code, profiles, gates, historical evidence, or authority were changed.

The earlier `OPUS_V3_SPOT_FARM_SCOPE.md` inventory substantially understates existing work. SPOT has executable settlement, liquidity, routing, typed buyback transitions, formal models, and a quarantined historical RISC0 implementation. FARM has an aggregate LP staking/reward kernel, generated reference, state serialization, and a composed LP/staking specification. Neither lane has been qualified by this review for the current isolated publisher. Related local-testnet reward writers remain relevant to whole-program mediation.

## Requirements and source precedence

The complete 262,425-byte `ZENODEX_M6_NORMATIVE_REQUIREMENTS_V1.json` was decoded and all 152 rows and 142 targets were traversed. Its 16 selected lane targets exactly match the capability manifest: ten SPOT and six FARM capabilities. `REQUIRED_UNRESOLVED` is the manifest's completion disposition; it is not an inventory of absent code.

| Source rows | Exact scoped requirement |
| --- | --- |
| `WF-02`, `BDD-005` through `BDD-008` | Authenticated current-pool settlement; output constraints; one atomic fill/fee outcome; replay protection. Maps to exact-in, exact-out, routing, atomic batch and fees. |
| `WF-03`, `BDD-009` through `BDD-012` | LP deposits and withdrawals, declared integer rounding, exact reconciliation of principal/fees/residues, and complete ownership when the pool closes. Maps to issue, burn, close and residues. |
| `RSE-007` | Pool creation binds both debits, reserves, locked and creator LP shares, fee profile, curve, nonce and duplicate-pool refusal. |
| `UP-12` | Governed SPOT/LP release choices, including curves, fees, routing, slippage, admission, close and residue disposition. |
| `UP-03` | All six FARM capabilities. No dedicated FARM workflow or BDD row is linked to these targets in this normative version. This is a specification coverage gap. |
| `INV-003`, `INV-004`, `INV-014`, `WF-17` | Per-asset conservation, complete claimant/reserve ownership, terminal drain and every mounted writer reaching the publication boundary or rejecting. |
| Adjacent `UP-01`, `UP-14`, `UP-15` | Fee percentages and hosting policy; retained-supply/burn parameters; ZDEX issuance/reserve/staking lifecycle. These affect composition, without transferring their ownership to FARM or SPOT. |

The normative file explicitly labels its ATDD donor as stale internal research provenance and its Luna donor as stale advisory evidence. It does not establish implementation, proof, mount or production qualification. Its `INV-005`, `BDD-006` and `BDD-010` retain a committed-business-failure interpretation that consumes ingress/history. V3 explicitly supersedes this for precommit rejection: a rejected attempt consumes no replay/history/effect state. A successor specification must resolve these rows against the selected V3 outcome contract; stale donor wording must not silently restore rejected-attempt consumption.

The adopted architectural choices recoverable from V3, the normative semantic anchors, and `ZDEX_ATOMIC_BUYBACK_ARCHITECTURE_DECISION_20260828.md` are:

- ZenoLedger owns economic ordering and publication; governance submits constrained commands.
- Existing wire/profile interpretations remain historical; asset quantities use integer atoms with declared precision.
- SPOT owns pool reserves. ZDEX tokenomics owns fee ingress/destinations, the buyback reserve and ZDEX supply. The primary buyback allocates fees, purchases and burns in one authenticated occurrence, with an ephemeral purchased-token port and no independent delayed budget object.
- Buyback spend follows `min(available reserve, per-command cap, authenticated route-safe limit)`; consensus height supplies cadence; the exact purchased amount is burned. A zero safe limit, insufficient governed minimum or unsafe price context rejects.
- The existing bounded Spot buyback release retains the entire rounded swap fee in its pool (`protocol_fee_share_bps = 0`). A nonzero share needs a separately owned value port and a successor release. This does not select the whole product's fee percentages.

The internal distribution/model documents explicitly describe candidates. Likewise, `zeno_ledger_tokenomics.py` labels its distribution amounts, LP reward weights and emission defaults as local-testnet choices. The research fee-allocation candidate explicitly leaves 2,500 bps unassigned and says its zero host share does not select zero compensation. None establishes an approved production FARM schedule or final fee split.

## Capability matrix

Status vocabulary here is deliberately narrow: `IMPLEMENTED_LOCAL` means executable source was inspected; `MODEL_PRESENT` means the named specification/proof source exists and its relevant statement was read; `MOUNTED_LEGACY` means a caller was traced in the retained non-V3 integration. `UNMOUNTED_V3` and `GAP` do not erase reusable work. Formal models were not rebuilt in this review.

| Lane/capability | Existing state, implementation and exact contract | Evidence and mount | Remaining closure |
| --- | --- | --- | --- |
| SPOT `pool_create` | `liquidity.create_pool`; `batch_clearing_create_pool._apply_create_pool_to_locals` and `settlement_replay_create_pool`: canonical assets/curve/fee pool identity, two debits, reserves, creator LP plus locked LP. | `IMPLEMENTED_LOCAL`, `MOUNTED_LEGACY` through `dex_engine.apply_ops`; liquidity tests replayed. Historical guest also implements creation. | Governed V3 pool admission/creation release, actual module/coordinator allocation producer, initialization and migration relation. |
| SPOT `exact_in_swap` | `cpmm.swap_exact_in` and `swap_exact_in_with_protocol_fee`; generated v8 kernel; strong settlement replay; bounded typed `zdex_spot_buyback_transition_v1/v2`. Fee is ceil, output is floor; reserve and signed-effect bounds are explicit in their respective versions. | Legacy execution caller; Python/Rust buyback twins and `ZDEXSpotBuybackTransitionV1.lean` are present. Historical guest implements a restricted exact-in subset. | General V3 user-swap module, selected authority/context and actual current receipts; buyback sibling/Oracle proofs do not complete every SPOT workflow. |
| SPOT `exact_out_swap` | `cpmm.swap_exact_out`, exact-out strong replay and routing. v8 owns sufficient/minimal gross input; wrapper enforces optional overdelivery limits and product nondecrease. | `IMPLEMENTED_LOCAL`, legacy `apply_ops`; `CpmmSwapV8ExactOutMinimality.swap_exact_out_sufficient_and_minimal` model present. | V3 exact-out module/refinement and governed quote-quality envelope. Historical Spot guest does not cover exact-out. |
| SPOT `governed_route` | `routing_exact_in/out` enumerate scoped candidates; maximize output/minimize input, then `routing_types.quote_key`. Quote-receipt checks exist in `dex_engine`; the typed buyback uses the profile-selected pool and authenticated price subject. | Executable routing and quote validation; numerous narrower routing proof sources. `MODEL_PRESENT` is not a route-completeness proof for arbitrary profiles. | Activate an exact supported route/search policy and bind every chosen path to V3 admission. Default `adaptive_v6` is a donor configuration, not approval to let callers choose authority. |
| SPOT `atomic_batch` | `batch_clearing.compute_settlement`, strong replay and `apply_settlement_pure`; `DexConfig.reject_settlements_with_rejected_intents=True` and `reject_settlement_public_boundary_error` refuse any rejected fill at the public DEX boundary. State is copied before application. | `IMPLEMENTED_LOCAL`, legacy node/Tau-plugin callers. Existing default engine bounds are 256 intents and 512 fills, with byte limits. | V3 outcome refinement, complete effect/head/history integration and selected release resource bounds. The 1–64 V3 epoch bound is a separate layer. No new atomic-vs-partial policy question is needed merely because clearing internals represent reject fills. |
| SPOT `lp_issue` | `liquidity.add_liquidity`, v7 ratio selection, `cpmm.compute_lp_mint`, LPTable and replay. Existing-pool mint is the minimum of the two floored proportional amounts; zero mint and bad minima reject. | Liquidity tests replayed; `CPMMInvariants` contains LP formulas and round-trip theorem; historical guest supports add-liquidity. | V3 claimant/LP custody projection, governed curve variants, staking coexistence and historical release migration. |
| SPOT `lp_burn` | `liquidity.remove_liquidity` and `settlement_replay_remove_liquidity`: owner LP debit, floored proportional asset credits and reserve/supply decreases. | Liquidity tests replayed; historical guest supports remove-liquidity. `zenodex_system_compose_v2.yaml` separately models stake-aware LP burn through mirror equalities. | Mount actual claimant authorization and stake/custody relation in V3. The aggregate model is not the deployed LPTable implementation. |
| SPOT `pool_close` | Existing creation credits `MIN_LP_LOCK=1000` to the zero-key LP row. Pool statuses are ACTIVE/FROZEN/DISABLED. The inspected remove path decreases reserves and supply; it does not implement a close transition or dispose of the locked row. | `GAP`: no close command found in the inspected intent/settlement/runtime dispatch graph. Positive ordinary withdrawals exist. | Resolve normative final-share closure against the locked minimum and define authorized terminal ownership/version transition. An empty or disabled pool is not evidence of a completed drain. |
| SPOT `fee_allocation` | Exact-in protocol-fee capture can remove a configured fee share from pool reserves and credit a named recipient. Separately, `fees.split_fee_with_dust_carry` returns a three-way accounting split; `zdex_fee_allocation_v1` owns a typed six-destination fee occurrence and named unallocated reserve. | Legacy capture/replay exists. Dust tests replayed. Typed ZDEX fee core/Rust/guest exist in their own lane. `dex_engine` explicitly does not pay the optional three-way split to balances. | Compose exact fee ingress with the ZDEX owner; select percentages/claimant policies; avoid counting an accounting result as a payment or counting LP fees twice. |
| SPOT `residue_terminal_disposition` | Swap and LP floor residues remain in reserves under existing math. Three-way split carries dust; typed ZDEX allocation names `protocol:fee-unallocated-reserve`. `FeeDustCarryConservation` proves scoped arithmetic identities. | `IMPLEMENTED_LOCAL` carry accounting; fee BVA/multistep conservation replayed. | Pool/claimant terminal ownership, shutdown of carry and unallocated-reserve spending authority. A named reserve closes current ownership, not its eventual drain. |
| FARM `lp_stake` | `vault._stake`, `VaultState.staked_lp_shares`; composed vault/LP models assert stake<=supply and mirrored equality. `DexState.vault` and snapshot encoding already retain aggregate vault state. | `IMPLEMENTED_LOCAL`, `MODEL_PRESENT`; generated-reference parity replayed. Runtime `dex.step` and `dex_engine.apply_ops` preserve `state.vault`; no vault command dispatch was traced there. | Per-owner stake records, authenticated LP debit/escrow, complete allocation projection and V3 producer/receipt/publisher mount. |
| FARM `stake_activation` | Aggregate vault activates stake immediately; the first stake distributes pending rewards. zUSD fee staking separately has pending stake and an epoch activation delay. | Donor behavior exists. zUSD is a different accounting lane and asset. | Select intended FARM eligibility/activation semantics; do not silently copy the zUSD delay or treat aggregate immediate activation as user-approved FARM policy. |
| FARM `emission_accrual` | `vault._deposit_rewards` advances a per-share index with integer carry; no-stake deposits remain pending. Local-testnet tokenomics has `build/validate_active_participant_emission_epoch_v0`, funded-reserve/refill/burn-capped monotone-rate budget and LP program weights. | `IMPLEMENTED_LOCAL`. No caller of the emission-epoch builder/validator outside their module was found in tracked Python sources. Tau halving and reward archetypes are additional models. | Authoritative epoch source, schedule, asset/funding owner, claimant accrual/debt and complete mounted emissions. Arithmetic existence does not select the economic schedule. |
| FARM `emission_claim` | `vault._harvest` returns a spendable reward effect. Local-testnet `append_tokenomics_reward_claim_v0` validates program/retained source receipt/claim key, debits controller tokens and credits recipient, then writes a new live state. LP activity is one eligible program. | Aggregate harvest parity replayed; a concrete legacy reward writer is traced to authenticated, enabled testnet HTTP intake. `production_security_claim=False` is explicit. | Per-claimant FARM authorization, replay debt, exact funded entitlement and V3 mediation. The local-testnet LP activity grant is not LP stake-time accrual. |
| FARM `farm_cancellation` | `_unstake` returns aggregate shares immediately; zUSD separately refuses fee unstake until fees are claimed. Neither defines FARM cancellation of future emissions and disposition of already-earned claims. | Partial donor behavior; `GAP` for the required complete lifecycle. | Stop/expiry authority, stake return, accrued reward ownership, effect pairing and replay. |
| FARM `farm_terminal_drain` | Aggregate unstake preserves reward balance/pending carry; the first future staker can receive carry under this donor model. No farm close/drain transition was found in its closed command family or traced dispatch. | `GAP`; complete bounded accounting is not complete terminal liability ownership. | Final claimant/remainder ownership, empty-stake behavior, cancellation/refund and historical-release drain/migration. |

`batch_clearing_create_pool` names several helpers; the relevant concrete writes are `lp_balances.add` at the creator/locked-share construction and corresponding `LPDelta` rows. The capability statement does not depend on a guessed generic module name.

## Important boundaries recovered by semantic tracing

1. **Legacy SPOT execution is real source, with a different publication boundary.** `src/integration/zeno_ledger_v0.py:837`, `tau_testnet_dex_plugin.py:1408`, and `tools/zeno_ledger_node.py:2040/2072` call `dex_engine.apply_ops`. This review establishes source reachability, not that those launchers are deployed or authorized for the selected V3 subject.
2. **The old Spot guest is present and quarantined.** `zk/state_proof_risc0` implements create/exact-in/add/remove over a restricted one-intent-per-transaction subset. Its documentation explicitly retains RISC0 1.2.6 quarantine and authority NONE. Historical proof smoke is not current release evidence, and this review neither rebuilt nor promoted it.
3. **The current V3 mount is ASSET-specific.** `isolated_asset_receipt_pipeline_v1` reconstructs ASSET_TRANSFER evidence, and `asset_transfer_epoch_allocation_v1` checks that restricted projection. A producer registry's missing SPOT/FARM integration is evidence of a mounting gap, not proof that settlement/staking algorithms are absent elsewhere.
4. **FARM cannot inherit authority from aggregate arithmetic.** `VaultState` has five aggregate numeric fields, no claimant, pool/asset identity, per-user debt, activation time or authenticated funding source. `harvest` receives an entry accumulator as ordinary command data. Completing the claimant/custody contract is required before mounting this arithmetic; conservation and authorization are separate obligations.
5. **Related reward mechanisms have distinct ownership.** zUSD fee staking in `zusd_monetary_bridge.py` includes pending activation, claims and fee-pool reconciliation; it is not automatically FARM emission policy. `FIRE reward_index_v1.zpl` exposes an exact supplied index parameter, not a stake/emission transition. Tau `token_v8_staking` and liquidity-mining archetypes are bounded predicate donors, not authenticated lifecycle implementations.
6. **The tokenomics writer must remain in W01/W11 scope.** `tools/zeno_ledger_node.py:4674/5272/5288` builds and publishes active-participant reward transfers. The HTTP branch at 6280–6310 requires write authentication and enabled testnet intake. This is a concrete mounted local-testnet value path even though no FARM-named writer exists. The emission policy module names `recommended/active_participant_emission_guard_v1.tau`; that path is absent from the exact tracked Git tree. Host-computed policy flags must not be reported as a replayed Tau emission proof.

## Only remaining economic decisions supported by this search

These are bounded recovery findings, not requests to reapprove existing equations. No accepted final selection was found in the reviewed normative/architecture/candidate sources. Further recovered user decisions take precedence.

| Decision | Existing choice to preserve | Actual unresolved selection |
| --- | --- | --- |
| SPOT release envelope (`UP-12`) | Canonical identity, integer formulas, deterministic quote tie-breaks, existing version bounds and fail-closed public batch behavior. | Which already-supported curve/fee/routing/quote-quality policies and resource envelope enter the new governed release. Reusing a donor version does not require inventing new math. |
| Pool terminal ownership (`UP-12`) | Locked initial LP and proportional withdrawal are existing version semantics. | Terminal disposition of the locked share, its reserves/fees/dust, surviving claims and historical-pool obligations. Do not silently reinterpret old balances. |
| Protocol fee entitlement (`UP-01`, adjacent `UP-14/15`) | Fee source/owner split, named residue, same-occurrence exact buyback/burn and profile-selected spend mechanism. | Governed destination percentages, actual qualified claimants, reserve spending/drain policy and numeric buyback envelopes. Candidate and local-testnet percentages are not approval. |
| FARM entitlement and funding (`UP-03`, adjacent `UP-15`) | Existing funded-reward and integer-carry mechanisms can be reused; zUSD monetary issuance stays in its monetary kernel. | Stake-time versus activity/usage eligibility, reward asset and authorized funding source, schedule/caps and authoritative epoch cadence. Existing aggregate, activity-grant and generic staking donors do not agree on one complete entitlement contract. |
| FARM activation/exit (`UP-03`) | Source-derived time and explicit claims are required; zUSD has its own already-versioned delay. | FARM activation delay/eligibility, withdrawal timing and treatment of already-accrued rewards on cancellation or expiry. |
| FARM terminal claims (`UP-03`) | Every atom must retain a claimant or named reserve owner. | Empty-stake pending rewards, final carry/refund recipient, future-accrual cutoff and terminal drain authority. Immediate first-staker carry in the aggregate donor does not settle this product decision. |

Missing receipt adapters, per-claimant state, ownership proofs, finite-width refinement, resource validation, authentication, migration and no-bypass evidence are implementation obligations. They are not reasons to ask the user to choose arbitrary constants or reinterpret settled authority boundaries.

## Executable evidence and separate BLS test review

The source classifier was run for the inspected core/adapter/test/document paths. The following unchanged tests were replayed locally, without a server or proof build:

```bash
python3 -m pytest -q -p no:cacheprovider \
  tests/core/test_vault_ref_parity.py tests/core/test_vault_defensive.py \
  tests/core/test_liquidity.py tests/core/test_fees_bva.py \
  tests/core/test_economic_command_signature_purpose_separation_v1.py
```

Result: **36 passed in 6.52 seconds**. The vault reference exists in this checkout and the suite did not skip: its seeded 500-step history is expressly bounded to stake<=100 and reward/pending<=1,000,000. It is not a proof of full-width runtime equivalence or claimant authorization. Liquidity tests cover ordinary positive withdrawals and reject boundaries, not terminal pool closure.

Independent read-only review of the parent's four new BLS separation cases found no blocking issue. The tests establish both-direction real-signature rejection after a status/profile registry change while preserving a same-scope positive control; they also check duplicate release identity refusal and different selected release messages within one profile. The last case checks real BLS directly rather than rerunning the full authentication entrypoint; the two preceding parameterized cases do exercise that entrypoint. Evidence roots remain synthetic fixtures. No new production signature authority or full pipeline qualification follows from these tests.

Lean, ESSO, Tau, Rust, RISC0, HTTP, deployment and whole-program gates were not rerun. No broad absence claim, live deployment claim, lane promotion or completion percentage is made. The next implementation packet can reuse the recovered kernels after the owning lifecycle/policy contract is fixed.

## Exact source anchors

All tracked paths discussed above were read from the stated HEAD without modification. The hash table below binds the most consequential semantic subjects and the separately untracked BLS test. The review does not adopt the Opus note's unsupported absence claims or candidate Research Kernel suggestions as authority.

| Path | SHA-256 |
| --- | --- |
| `docs/research/ZENODEX_M6_NORMATIVE_REQUIREMENTS_V1.json` | `29d67d2c8ebd35d6e0003927c73043f3f282efe16b780b4493504d1d00db390f` |
| `docs/research/ZENODEX_M6_CAPABILITY_MANIFEST_V1.json` | `34930be9d4d69c4c46c7c97f57fd492d4c95061f8960f936261a8a3415d5db95` |
| `docs/research/ZDEX_ATOMIC_BUYBACK_ARCHITECTURE_DECISION_20260828.md` | `730ff45ab198de16c13789760ddb3eca58638c6f3a8819a4e8cbd1dbdbee3bf2` |
| `docs/research/ZDEX_HYPERDEFLATION_V1_20260821.md` | `dcf7209eccab9e022950053ff5e1fdb85ededdb20410123697ea94ce653554f9` |
| `src/core/liquidity.py` | `63035d26cab4cc1ac45fb4996edaf5ce176f9e62903c043f1db6048fcddaea26` |
| `src/core/cpmm.py` | `5b216df8acf54f1bdc2241d7e9ae30291486e13de5ac8f59f2f2cce4a8e0c5d5` |
| `src/core/dex.py` | `dc3c66fd95dc22df717626f904111f03f83c7901254146f351d547192ed5f993` |
| `src/core/batch_clearing_create_pool.py` | `2010830fa6002bdccb2f9214253a731081805cef7929ebc90761443d21ca618d` |
| `src/core/settlement_replay_remove_liquidity.py` | `b89b49c75878074f30e13a2c6536ce5b9a07e81ee203c3a1d9cfe7cfecff58e5` |
| `src/core/routing_types.py` | `450163690f06ebd360854a5cac77a2050bea3bc3737d9c26a0771815b80f4bbe` |
| `src/core/routing_exact_in.py` | `1dde36da44e09dc5bac5c6959ff733df57a3ce3ebbd5131eb057aa6a2df320f6` |
| `src/core/routing_exact_out.py` | `bd6160481957a03ad41710ba41a0d0f8720be8cda3c0db2752ca7ec531b1cdd6` |
| `src/core/zdex_spot_buyback_transition_v2.py` | `9e71420028c4a2f6f7714c34c96f11b721948bb5417e55460b293fe18b1779db` |
| `src/core/vault.py` | `e8f3122ff5becefbc898f379ebc9511d45d31b48985e9154e716748b3b65019a` |
| `src/kernels/dex/vault_manager.yaml` | `9b9bd9077e4efd877cec5671682c968269af69c0cac3c92ad9c753bd5c30301c` |
| `src/kernels/dex/zenodex_system_compose_v2.yaml` | `7912b5022895d7995297bc65fd6e48524ec43613ff94b9d4f522f93b39d5a279` |
| `generated/vault_python/vault_manager_ref.py` | `fd40268bb5130b4ddb061c9a46dd826b9d7253c00ad01598a609ab9862c9a4ca` |
| `src/integration/dex_engine.py` | `0fa79bbc8bd9d301448a2fd694461cd005486886b6557ca6f45fd5a7adb1dcf3` |
| `src/integration/zeno_ledger_tokenomics.py` | `607a53b3c083d3a913135f143735285b27145990122d7c6c9ddffc25fcb81d3e` |
| `tools/zeno_ledger_node.py` | `0fd4db61b0a8240a09f83c6aa43cfd4bce2e13fbb708388dca30542a71e81c1b` |
| `src/integration/zusd_monetary_bridge.py` | `8a0c49e3a78b31c92910c08c33dec5ff4a3b8fca2196249c8be5275c4ae7f9d5` |
| `docs/zenodex_spot_state_proof_risc0_v1.md` | `7a1bb021b49d575039e714d5da20c69c68d118449eec0b1031acff9ead46acbe` |
| `tests/core/test_economic_command_signature_purpose_separation_v1.py` | `0ec1a948496c355fa0c2342ea0de9a934b6d5d10da508777ebb74c9080dcaebc` |
