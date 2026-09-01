# Codex audit receipt: candidate C1 at P = 3b3528bacc13c65bc386dacff7e3ee6943605ca1

Reviewer: Codex (`codex exec`, read-only, detached worktree `/tmp/zenodex-formal-core-review-p-3b3528bac`).
Date: 2026-09-01. Subject: P = 3b3528bacc13c65bc386dacff7e3ee6943605ca1 (tree 8154e9153a7871c316e6b729662df03b2a3b3ec8), S = 28138402baa8d4bc46098075d9c2b3febcb60c65, base fd409ba6f7da8f0ec3e0220a04b7406d69a8cb85.
Verdict: Grade C, REVISE. Disposition: both findings are repaired by candidate C1' (the next source commit after this receipt); the grade is advisory and grants no authority.

Verbatim report follows (the temporary adversarial clones it names lived under /tmp/codex-c1-* and are not part of the repository).

---

+    ($name:ident) => {
+        #[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
+        pub struct $name {
+            pub obligation_id: String,
+            pub lane_id: LaneIdV1,
+            pub claimant: String,
+            pub asset: String,
+            pub amount_atoms: u128,
+            pub status: TerminalObligationStatusV1,
+        }
+    };
+}
+
+define_live_terminal_obligation_v1!(TerminalObligationV1);
+
 impl TerminalObligationV1 {
     pub(crate) fn validate(&self) -> AbiResultV1<()> {
         validate_token_v1(&self.obligation_id, "terminal obligation id")?;

tokens used
440,393
# Grade: C — REVISE

The exact C1 subject is clean, correctly chained, claim-limited, and passes every prescribed verification. The nine Lean additions are genuine and honestly documented, including the definitional `Iff.rfl` results. However, the admission mechanism has a P1 structural-scan survivor that passes a complete alternate S/P chain, fresh replay, and all 136 checker tests while the compiled Rust type violates the claimed schema. A second survivor defeats the claimed proof-replay-record mutation killer. These prevent an A/B grade despite the exact C1 sources themselves being non-promoting and internally consistent.

## Findings

### P0 — None

No effective authority escalation, value movement, production promotion, or `formal_core_complete=true` path was found.

### P1 — Rust admission checks a textual decoy, not the compiled type

Files: [o008_formal_cycle_admission_v1.py:1121](/tmp/zenodex-formal-core-review-p-3b3528bac/tools/o008_formal_cycle_admission_v1.py:1121), [o008_formal_cycle_admission_v1.py:1175](/tmp/zenodex-formal-core-review-p-3b3528bac/tools/o008_formal_cycle_admission_v1.py:1175), [o008_formal_cycle_admission_v1.py:1359](/tmp/zenodex-formal-core-review-p-3b3528bac/tools/o008_formal_cycle_admission_v1.py:1359), [o008_formal_cycle_admission_v1.py:642](/tmp/zenodex-formal-core-review-p-3b3528bac/tools/o008_formal_cycle_admission_v1.py:642), [test_check_o008_formal_cycle_v1.py:341](/tmp/zenodex-formal-core-review-p-3b3528bac/tests/test_check_o008_formal_cycle_v1.py:341)

Exact statement: the regex/balanced-brace scanner does not interpret `cfg` or macro expansion. A `#[cfg(any())]` decoy with the expected fields and `deny_unknown_fields`, followed by a macro-generated live type without that attribute, is admitted. Replay contains no Rust compile or runtime-schema command.

Adversarial chain:

- S′: `21b05f7c23a379bb0330be4d804c47eb598cab75`
- P′: `3e39138fe45eb14dd6d8f43313c282d767f9e202`
- P′ changes only the two packet files.
- Checker: `ok=true`, `packet_admitted=true`.
- Fresh replay: `EXECUTED_PASS`.
- Checker suite: `136 passed`.
- Compiled Serde behavior: `unknown_field_accepted=true`.

Reproduce:

```bash
cd /tmp/codex-c1-rust-survivor-HEBMXM/repo
PY="/home/trevormoc/Downloads/Autonomous Tau DEX/.venv/bin/python"

"$PY" tools/check_o008_formal_cycle_v1.py --root "$PWD" --replay \
  --python "$PY" --esso-python /usr/bin/python3 \
  --esso-pythonpath /home/trevormoc/Downloads/ESSO

"$PY" -m pytest -q -p no:cacheprovider tests/test_check_o008_formal_cycle_v1.py

cargo run --quiet \
  --manifest-path zk/global_settlement_abi_v1/Cargo.toml \
  --example adversarial_unknown_field
```

Required repair: bind admission to the compiled declaration or reject all `cfg`/macro indirection around critical ABI records; add Cargo compilation plus strict unknown-field runtime vectors to replay; add this cfg-decoy/macro-live regression. The Python scanner should likewise reject inheritance and unreachable-return tricks.

### P2 — A well-shaped fabricated author replay record survives

Files: [o008_formal_cycle_admission_v1.py:1439](/tmp/zenodex-formal-core-review-p-3b3528bac/tools/o008_formal_cycle_admission_v1.py:1439), [o008_formal_cycle_admission_v1.py:1458](/tmp/zenodex-formal-core-review-p-3b3528bac/tools/o008_formal_cycle_admission_v1.py:1458), [o008_formal_cycle_admission_v1.py:1959](/tmp/zenodex-formal-core-review-p-3b3528bac/tools/o008_formal_cycle_admission_v1.py:1959), [test_check_o008_formal_cycle_v1.py:233](/tmp/zenodex-formal-core-review-p-3b3528bac/tests/test_check_o008_formal_cycle_v1.py:233), [THV1 packet:399](/tmp/zenodex-formal-core-review-p-3b3528bac/tests/evidence/test_hygiene/THV1-20260901-o008-formal-cycle-admission-v2.json:399)

Exact statement: the named mutation “fabricate an executed proof-replay record” kills only an incomplete record. `toolchain` has no schema validation and is never compared during fresh replay. A direct child of exact S containing `lean=999.0`, forged solver versions, and an authority-shaped extra key is admitted and obtains `EXECUTED_PASS`.

Adversarial P′: `0ece665fdf718a3516252e1e144cd2b367376244`, parent exact S.

Reproduce:

```bash
cd /tmp/codex-c1-author-record-8qhC7v/repo
PY="/home/trevormoc/Downloads/Autonomous Tau DEX/.venv/bin/python"

jq '.proof_replay.author_record.toolchain' \
  docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json

"$PY" tools/check_o008_formal_cycle_v1.py --root "$PWD" --replay \
  --python "$PY" --esso-python /usr/bin/python3 \
  --esso-pythonpath /home/trevormoc/Downloads/ESSO
```

The effective report claim ceiling still remains `NONE`, limiting this to evidence falsification rather than authority escalation.

Required repair: impose exact per-command comparable schemas and an exact toolchain schema, compare every toolchain field during fresh replay, reject unknown/nested authority-shaped keys, and replace the incomplete mutation with a fully shaped forged-record test.

### P3 — None

No additional low-severity defect warrants a separate finding.

## Verification record

Exact identity:

- P: `3b3528bacc13c65bc386dacff7e3ee6943605ca1`
- P tree: `8154e9153a7871c316e6b729662df03b2a3b3ec8`
- S: `28138402baa8d4bc46098075d9c2b3febcb60c65`
- S parent: `fd409ba6f7da8f0ec3e0220a04b7406d69a8cb85`
- P has exactly one parent and changes only the JSON/Markdown packet.
- THV1 does not pin either packet file.
- Final tracked/untracked status output was empty.

Prescribed commands:

1. `git status --porcelain | grep -v '^??'` — exit `1`, empty output; correct grep result for no tracked changes.

2. `git diff-tree --no-commit-id --name-status -r HEAD^ HEAD` — exit `0`; exactly the two packet files, both `M`.

3. Checker without replay — exit `0`; `ok=true`, admitted/applicable, replay `NOT_RUN`.

4. Checker with replay — exit `0`; `EXECUTED_PASS`; all eight runs exit `0`, Lean 25 theorems, Lean gate 6, ESSO gate 18, prior gate 136.

5. Builder `--check --replay` — exit `0`; `"ok":true,"drift":[]`.

6. Combined checker/Lean pytest — exit `0`; `142 passed in 44.29s`.

7. ESSO pytest — exit `0`; `18 passed in 16.47s`.

8. Direct Lean warnings-as-errors — exit `0`; empty output.

9. Ruff — exit `0`; `All checks passed!`.

10. Mypy strict — exit `0`; `Success: no issues found in 4 source files`.

11. Test hygiene — exit `0`; `ok=true`, `changed_path_count=2`, `critical_path_count=0`.

Hand-recomputed S pins:

```text
src/core/global_economic_state_effect_refinement_v1.py
2c80fe364241de0fa2c93c258767dd93ad65233fbb58de71af398b3b5c1c2d54

zk/global_settlement_abi_v1/src/global_economic_state_effect_refinement.rs
44352e36e147c59ca397e571237d48eebd91787066df26fb7a5b65b2a78b2672
```

Executing tool hashes matched S:

- Checker: `e8f131c750dc150f9fc176b2c07f258a6038a5c223de469ae77c24cc4e9307e6`
- Core: `5fcffbc760b1529a15974378ee1af4822bb56c4cf401daf5ee68103ff6401f26`
- Shell: `f4355f5636da2ef7c1cc26d69fcf4ee8fc71f55b551a3a475b754022b5a0478b`
- Lean scanner: `44a7c67142955ad3b7a803ab599d31ca8754d0f9cdd795588ea9745f58239fc4`

The prescribed matrix ran with the repository read-only and temporary/cache storage outside it. Nothing was written under `/dev/shm`.

## Lean and semantic conclusions

All nine new theorems are valid and honestly described:

- Four definitional results use `Iff.rfl`/`rfl`; their documentation explicitly discloses that.
- `overCollateralised_isBacked_notExact` correctly separates R1 from R3.
- The concrete `noUnclassified` witness is accurately documented as composing with the preceding counterexample.
- The three forward weakening theorems are genuine derivations.
- No hidden tautology beyond the disclosed definitional results was found.
- Python/Rust necessary-check arithmetic, pre/post enforcement, checked-u128 behavior, and rejection ordering matched.
- No hidden I/O was found in the pure core.

## User decisions

| Decision | Result |
|---|---|
| Claimant-free reserve partition | Honored exactly |
| New control-domain vocabulary; V1 wire bytes stable | Honored |
| O-008A unattested | Honored |
| UP-01..UP-20 unresolved and not fixture-selected | Honored |
| Authority `NONE`; `formal_core_complete=false` | Honored |

## Nonclaims and residual risks

- Exact C1’s current Rust type does have `deny_unknown_fields`; P1 demonstrates an admission-gate survivor, not a mounted C1 runtime exploit.
- Exact C1’s recorded toolchain values were independently consistent with Python `3.12.3`, Lean `4.27.0`, and ESSO commit `7f80c621…`; P2 concerns what admission permits.
- O-008 remains open, with `0/12` value-movement gates.
- The all-lane allocation certificate remains unimplemented, unattested, and unmounted.
- ESSO remains a bounded one-asset/two-domain/two-claimant model.
- Lean does not establish finite-width runtime parity, cryptographic binding, or settlement authority.
- `EXECUTED_PASS` is narrower than the complete audit matrix: it runs neither Cargo validation nor the 136 admission-checker tests.
- This grade is advisory and grants no authority.


