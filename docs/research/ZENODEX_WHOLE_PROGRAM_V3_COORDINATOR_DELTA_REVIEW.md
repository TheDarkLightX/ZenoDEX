# ASSET coordinator signed-delta review and reward-writer inventory follow-up

Date: 2026-09-05. Independent source review against HEAD `2507a99f0f3dd4811dc12114a421c1ad1bc7cf73` and the three candidate Rust files hashed below. This reviewer did not implement these changes. No code, gate inventory or release metadata was changed by this review. The parent owns the combined Cargo gate; no competing Cargo process was started.

## Signed-difference repair

The repair is arithmetically correct. Absolute holdings have type `u128`; their difference, rather than each absolute, must fit the `i128` effect domain. `asset_lane_coordinator.expected_movement_deltas` now calls the existing `global_economic_state_delta.checked_signed_delta_v1(post, pre)`. The helper body is unchanged and its visibility becomes only `pub(crate)`.

For `post >= pre`, unsigned subtraction is defined and conversion accepts exactly differences through `i128::MAX`. For `post < pre`, unsigned magnitude is defined; the special magnitude `2^127` returns `i128::MIN`, smaller magnitudes are converted and negated, and larger magnitudes return `InvalidBounds`. No subtraction wraps and no branch negates `i128::MIN`.

All previously accepted coordinator deltas are unchanged: when both absolutes fit the old nonnegative `i128` casts, the mathematical difference lies between `-i128::MAX` and `i128::MAX`, and the new helper computes that same difference. Canonical map keys, zero omission, journal construction and effect encoding are unchanged. The improvement permits unchanged large holdings and representable small movements between large holdings. This statement does not equate all old refusals with valid successor transitions; other coordinator checks still apply.

The new test exercises the actual coordinator helper with both account and non-account custody rows. Its independently stated 16 boundary cases cover zero, unchanged `2^127` and `u128::MAX`, one-atom movements on either side, positive MAX, negative MIN and adjacent unrepresentable magnitudes. The retained red log `zenodex-v3-asset-coordinator-signed-delta-red02.log` fails on unchanged `2^127`, where the old implementation returned failure instead of an empty movement map. This review inspected the log; it did not rerun that Cargo command.

## CDR-01: failed derivations must not compare equal

Status at the initial reviewed candidate: **OPEN, pre-existing caller defect**. The signed-difference helper repair is suitable, but the caller's rejection behavior needs a separate fail-closed correction before this packet closes.

`conservation_reject` compares two `Option<BTreeMap<...>>` values directly. If both calculations fail, both values are `None` and equality succeeds. The expected-map calculation can fail on an unrepresentable signed movement; the effect-map calculation can fail on an incompatible movement-kind/accounting-domain combination. The inspected `EconomicEffectRowV1.validate`, `GlobalEconomicEffectPlanV1.validate` and `effect_shape_reject` do not themselves eliminate the latter domain failure. Therefore absence of both maps must not serve as state/effect agreement.

Required correction: explicitly reject either unsuccessful derivation with the existing `STATE_EFFECT_MISMATCH` outcome, then compare the two successfully derived maps. The existing `reject` constructor binds identical pre/post lane roots and empty effects. Retain a harmless unit sentinel that verifies failed derivations cannot become agreement, plus the existing signed-range controls. No operational reproduction, serialized submission or adversarial publication was created in this review.

This source finding is scoped to the pure coordinator. It does not demonstrate a bypass of the separately authenticated module receipt, profile, publisher or operating-system trust boundary. The Python coordinator computes mathematical integer differences and compares an optional effect map to a concrete dictionary; it does not have the same failed-map equality expression.

## Release implications

There is no wire/journal schema change and no new receipt authority. Existing accepted journals remain interpretable under their original releases. The coordinator execution source has changed, so a new qualification must bind the rebuilt ELF, measured image, selected module/coordinator compatibility and exact source/toolchain subject. Old genuine receipts remain evidence for their old image. New image equality cannot be assumed from unchanged journal schemas or host-only tests. The current gate does not constitute a universal Rust proof or a new real RISC0 qualification.

## Reward writer: present root sink, missing command-level mapping

The reward publication path was already represented at two existing W01/M6 levels:

- `ZENODEX_WHOLE_PROGRAM_V3_AUTHORITY_DISCOVERY.md:53` names `_build_tokenomics_reward_claim_block_from_body_v0`; its lane map at line 86 places node reward/burn functions under ZDEX tokenomics.
- `tools/m6_value_sink_manifest_v2.json` contains `zeno_ledger_node___write_json__atomic_replace`. Its rationale explicitly includes tokenomics reward-claim blocks. Its classification is `DURABLE_VALUE_STATE`, mediation is `UNMEDIATED_DEPLOYED_WRITER`, and `release_binding` is null. This is the inventory's declared posture, not a new live-deployment observation.

The exact source path is:

```text
make_node_http_server_v0
  /api/tokenomics/active-participant/claim or /api/tokenomics/claim
  -> write authentication + enabled testnet intake
  -> append_tokenomics_reward_claim_v0
  -> _append_tokenomics_reward_claim_v0_locked
  -> _build_tokenomics_reward_claim_block_from_body_v0
  -> _write_json for artifacts + _write_live_state for the live pointer
```

The block builder derives an earlier accepted source receipt, eligible participant/action, program budget and already-claimed keys, then debits the program controller's token balance and credits the recipient. Exact transaction-ID retry is checked before building another claim. These are source-level controls, not complete durability, authorization or terminal-lifecycle qualification.

`tools/m6_writer_inventory_manifest_v1.json` has 27 command-entry rows and no `tools/zeno_ledger_node.py` entry. Its checker scans only `src/**/*.py` for already-covered symbol names. Accordingly, a structural PASS cannot discover this missing command entry, even though the lower sink census already records its file publication. The command coverage schema has lane/workflow fields but no capability-specific ownership or lifecycle edges.

The accurate additive inventory packet should:

1. Add explicit legacy command entries for the public reward append, its locked implementation and the reward block builder, with exact symbol references and evidence markers linking the existing call chain. Preserve `commit_port_route=none`, adapter `LEGACY_ONLY`, empty assurance statuses and OPEN release/terminal/proof/effect/route gaps. `UNMOUNTED_LEGACY` here means unmounted from M6, not absent from legacy testnet intake.
2. Associate those entries with the already inventoried `_write_json` sink; avoid claiming discovery of a new durable root sink or duplicating its economic effects. Recording its semantic consumers is an inventory refinement, not mediation.
3. Add a semantic mapping for `legacy/tokenomics-active-participant-reward-claim/v0`: ZDEX reserve lifecycle is the accounting owner. Program eligibility refers to source SPOT LP activity, zUSD Stability Pool/vault activity, perps activity, Oracle reports and proof work. Those source-lane dependencies do not mean the reward payout writes each source lane.
4. Label LP activity payouts as a potential FARM `emission_claim` requirement linkage whose entitlement remains unresolved. They are fixed activity grants under local-testnet programs, not evidence of implemented stake-time accrual, activation, cancellation or farm terminal drain. Likewise, an activity payout is not automatically a ZDEX staking claim.
5. Keep `WF-17` mediation/restart/terminal requirements explicit. The normative successor needs a dedicated active-participant payout workflow or capability obligation if the existing FARM/ZDEX contracts do not cover this product behavior. Existing all-lane placeholder rows do not discharge that gap.

No inventory, classification, capability namespace, checker scan scope, live path or gate snapshot was modified. A later approved inventory edit should retain the known-name scanner's stated bounds or separately extend its launcher roots with a regression; it must not claim deployment completeness from these entries.

## Evidence

Read-only `python3 tools/check_m6_writer_inventory.py --json` returned structural `ok=true`, zero findings and `release_ready=false`. Its retained report is `zenodex-v3-reward-writer-inventory-review01.json`, SHA-256 `02a39f28c4cb36fbfb2947bf0d6ee9bfd6018090470eda5005991b2e94e7b1b2`. This positive control illustrates the declared scanner scope; no malformed input or bypass test was run.

| Subject at initial review | SHA-256 |
| --- | --- |
| `zk/global_settlement_abi_v1/src/asset_lane_coordinator.rs` | `c53ba97b37ccabad2ce898cacb320777c61fa333e3fb2fb686d47c0331361ae0` |
| `zk/global_settlement_abi_v1/src/global_economic_state_delta.rs` | `3d9fc36a2af91853a3add785bb1f29a6ba3fcbea111fd4689303e045e935a530` |
| `zk/global_settlement_abi_v1/src/asset_lane_coordinator_signed_delta_tests.rs` | `62492d46b2d847766dcfcb19aaccdff301f161dfabf8f87668c127bf510c94d7` |
| `tools/m6_writer_inventory_manifest_v1.json` | `a0f8bd4c11660aa4d614a089b252ac5403d7cee0d4cb73454afc121a4bfa0b9f` |
| `tools/m6_value_sink_manifest_v2.json` | `521470b5e59b5bc3ba441216ae3bc69038f383422f8647da366b9c0b3c730e1e` |
| `tools/check_m6_writer_inventory.py` | `f44c42a9caaa42f9dae53e8852dd211773d3ed2d14f9423983434d35f151fd33` |
| `tools/zeno_ledger_node.py` | `0fd4db61b0a8240a09f83c6aa43cfd4bce2e13fbb708388dca30542a71e81c1b` |

No Cargo, Lean, ESSO, Tau, RISC0, HTTP or deployment test was launched by this reviewer.

## CDR-01 closure supplement

The parent repaired `movement_derivations_match` to accept only two successful maps whose contents agree. `conservation_reject` calls that helper and retains `STATE_EFFECT_MISMATCH`, identical pre/post roots and empty rejection effects. Independent source review confirms every failed-side combination now refuses, while empty-map and nonempty-map agreement remain valid.

The parent's benign sentinel failed first at `movement_derivations_match(None, None)` in `zenodex-v3-asset-coordinator-derivation-red01.log`, SHA-256 `8be65b3cfd6263a56d3d2db5400dea91ee82e4c72372a36a8817d5d44ef1d2c3`. The completed six-target test log, `zenodex-v3-asset-coordinator-complete-green01.log`, SHA-256 `fe7b5910bc8ae2be2ee152d1fcb352fadf7de6fef1ba0f67ffde71e30733becd`, reports both new tests passing and all six target result summaries passing. Clippy completed without warnings in `zenodex-v3-asset-coordinator-complete-clippy01.log`, SHA-256 `a63ed18a713c4e7d6f94b47189b556ee44d0b9677b1073a5cbee0c88a0eb991a`. This reviewer independently read these retained logs; execution was owned by the parent.

Final reviewed coordinator SHA-256: `63f594266bf0cab03769bca264a62603f0d3a6e3b14fdbe11650cdf4a64e2169`. Final new test SHA-256: `e20fab34c3c8b06b6332cbd5b80c01dba04b1d20511577790c4a0ebd1ad17d07`. The signed-delta helper remains at the earlier hash. **CDR-01 is closed for this exact source/test subject.** Release/image and runtime proof nonclaims above remain unchanged.
