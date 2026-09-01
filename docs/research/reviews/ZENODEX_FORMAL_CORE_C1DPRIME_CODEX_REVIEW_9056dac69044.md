# Codex audit receipt: candidate C1'' at P = 9056dac69044772aab9316637a68ec94265fe885

Reviewer: Codex (`codex exec`, read-only audit in detached worktree `/tmp/zenodex-formal-core-review-p-9056dac69`; adversarial clones under `/tmp/codex-c1dprime-R607Mw`).
Date: 2026-09-01. Subject: P = 9056dac69044772aab9316637a68ec94265fe885 (tree dcdd90fd38a72622eb7bd8d8724de9899d495fba), S = 6358da52f5a4235f6928dda0bf1bdee92d862dd2, parent chain R4 = fd59705426b50787e813d62b7c6bd30a371f08df.
Verdict: Grade D, REVISE. Disposition: the Rust P1 is targeted by candidate C1''' (P = da227713788dac83853f92177892b14268433d6a, cut before this receipt landed) and is re-verified against the exact survivor S' = 6c8499030e12b9d7c724f63523e4dc99abc1dbc3 in the next candidate; the Lean statement P1, both P2s, and the negative regressions are repaired by candidate C1'''' (the next source commit after this receipt). The grade is advisory and grants no authority.

Verbatim report follows (the adversarial clones and patches it names are not part of the repository).

---

# Grade: D

The exact S5 source is internally coherent and every prescribed check passes, but the admission mechanism is not class-closed. I constructed two independent S/P chains that retained the required two-file packet commit and passed all 15 replay commands: one compiled a widened Rust container behind an imported deserializer and no-op projection gate; the other replaced `noUnclassified_premise_is_necessary` with `True`. Therefore C1 P1 is **not closed as a class**. C1 P2, forged author records, **is closed under fresh replay** through the exact schemas and full comparison; without `--replay`, the disclosed shape-only caveat remains.

This grade is advisory and grants no authority.

## Findings

### P0 — None

No authority escalation or direct value-movement path was found.

### P1 — Rust projection closure and gate non-vacuity remain bypassable

Files: [admission core:1536](/tmp/zenodex-formal-core-review-p-9056dac69/tools/o008_formal_cycle_admission_v1.py:1536), [admission core:1643](/tmp/zenodex-formal-core-review-p-9056dac69/tools/o008_formal_cycle_admission_v1.py:1643), [admission core:1671](/tmp/zenodex-formal-core-review-p-9056dac69/tools/o008_formal_cycle_admission_v1.py:1671), [admission core:1928](/tmp/zenodex-formal-core-review-p-9056dac69/tools/o008_formal_cycle_admission_v1.py:1928), [Rust gate:8](/tmp/zenodex-formal-core-review-p-9056dac69/zk/global_settlement_abi_v1/tests/v1_projection_gate.rs:8).

Exact statement: the checker counts the required macro invocation without requiring module scope or binding it to the function selected by `deserialize_with`. It also permits new crate modules. Gate validation pins test names and field tables, not test bodies.

Mounted survivor:

- S′: `6c8499030e12b9d7c724f63523e4dc99abc1dbc3`
- P′: `7c3d269bc1e3dd2fe565cb8721c13cdd2a086c70`
- P′ changes only the JSON/Markdown packet.
- A block-local macro invocation is the decoy.
- The live deserializer is imported from a new module and removes `liability_domain`.
- All seven pinned Rust test names remain, but their bodies are no-ops.
- Checker replay: `EXECUTED_PASS`, all 15 commands.
- Compiled probe: `WIDENED_TERMINAL_ROW_ACCEPTED`.

Reproduce:

```bash
cd /tmp/codex-c1dprime-R607Mw/repo
PY="/home/trevormoc/Downloads/Autonomous Tau DEX/.venv/bin/python"

"$PY" tools/check_o008_formal_cycle_v1.py --root "$PWD" --replay \
  --python "$PY" --esso-python /usr/bin/python3 \
  --esso-pythonpath /home/trevormoc/Downloads/ESSO

CARGO_TARGET_DIR=/tmp/codex-c1dprime-repro-target CARGO_INCREMENTAL=0 \
  cargo test --manifest-path zk/global_settlement_abi_v1/Cargo.toml \
  --offline --locked --test codex_widened_probe -- --nocapture
```

Required repair: parse or compiler-bind the actual resolved deserializer; require the macro invocation at module scope; close the compiled module graph; and validate gate assertions/behavior rather than names and constants. Add this exact survivor as a negative regression.

### P1 — Lean statement semantics are self-pinned, not normatively closed

Files: [admission core:1814](/tmp/zenodex-formal-core-review-p-9056dac69/tools/o008_formal_cycle_admission_v1.py:1814), [admission core:1826](/tmp/zenodex-formal-core-review-p-9056dac69/tools/o008_formal_cycle_admission_v1.py:1826), [checker test:316](/tmp/zenodex-formal-core-review-p-9056dac69/tests/test_check_o008_formal_cycle_v1.py:316), [v6 hygiene packet:524](/tmp/zenodex-formal-core-review-p-9056dac69/tests/evidence/test_hygiene/THV1-20260901-o008-formal-cycle-admission-v6.json:524).

Exact statement: theorem names and newly computed statement hashes are recorded, but expected theorem types are not independently fixed. The claimed mutation killer detects a stale packet; it does not reject a freshly regenerated packet for a weakened theorem.

Mounted survivor:

- S″: `d40c9ac30a1e916b9253d84a267e5355c626df70`
- P″: `2dc6492fa2fe0e38badffb08456fe044d5e07701`
- `noUnclassified_premise_is_necessary : True := by trivial`
- P″ changes only the packet JSON/Markdown.
- Checker replay: `packet_admitted=true`, `current_applicable=true`, all 15 commands `EXECUTED_PASS`.

Reproduce:

```bash
cd /tmp/codex-c1dprime-R607Mw/leanrepo
git show HEAD^:lean-mathlib/Proofs/GlobalClaimantCustodyRelationV1.lean |
  sed -n '255,266p'

PY="/home/trevormoc/Downloads/Autonomous Tau DEX/.venv/bin/python"
"$PY" tools/check_o008_formal_cycle_v1.py --root "$PWD" --replay \
  --python "$PY" --esso-python /usr/bin/python3 \
  --esso-pythonpath /home/trevormoc/Downloads/ESSO
```

Required repair: bind load-bearing theorem types to independently trusted hashes or compile a fixed harness asserting their exact propositions. Mutation tests must regenerate an S/P chain and require rejection.

### P2 — Both appended hygiene packets contain false `killed_by` claims

Files: [v6 packet:684](/tmp/zenodex-formal-core-review-p-9056dac69/tests/evidence/test_hygiene/THV1-20260901-o008-formal-cycle-admission-v6.json:684), [golden-v3:193](/tmp/zenodex-formal-core-review-p-9056dac69/tests/evidence/test_hygiene/THV1-20260901-claimant-backing-guard-golden-v3.json:193), [claimed reserve killer:105](/tmp/zenodex-formal-core-review-p-9056dac69/tests/core/test_global_claimant_backing_guard_v1_golden.py:105).

Exact statement:

- v6’s vacuous-gate and weakened-Lean-statement killers stay green under mounted survivors.
- golden-v3 claims the field-name test kills counting reserves as backing. Feeding reserves into the existing custody fold adds no field, so that test passes while `excludes_reserves_from_backing` fails.

Reproduce the golden mismatch:

```bash
cd /tmp/codex-c1dprime-R607Mw/repo
git apply /tmp/codex-c1dprime-R607Mw/golden-reserve-mutation.patch

PY="/home/trevormoc/Downloads/Autonomous Tau DEX/.venv/bin/python"
"$PY" -m pytest -q -p no:cacheprovider \
  tests/core/test_global_claimant_backing_guard_v1_golden.py::test_view_has_no_reserve_or_balance_column
# exit 0

"$PY" -m pytest -q -p no:cacheprovider \
  'tests/core/test_global_claimant_backing_guard_v1_golden.py::test_vector_replays_state_view_root_and_outcome[excludes_reserves_from_backing]'
# exit 1: mutated outcome ACCEPT instead of REJECT
```

Required repair: execute each declared mutation and require its named node to fail. Split compound mutation descriptions and map reserve/message/precedence mutations to behavioral cross-language vectors.

### P2 — Cargo replay inherits unpinned external configuration

Files: [shell:38](/tmp/zenodex-formal-core-review-p-9056dac69/tools/o008_formal_cycle_shell_v1.py:38), [shell:313](/tmp/zenodex-formal-core-review-p-9056dac69/tools/o008_formal_cycle_shell_v1.py:313), [forbidden paths:79](/tmp/zenodex-formal-core-review-p-9056dac69/tools/o008_formal_cycle_admission_v1.py:79), [Rust version command:875](/tmp/zenodex-formal-core-review-p-9056dac69/tools/o008_formal_cycle_admission_v1.py:875).

Exact statement: repository Cargo configs are rejected, but replay passes through `HOME`, `CARGO_HOME`, `PATH`, and Rustup settings. Cargo can therefore read an unpinned home config or wrapper. Replay records Cargo’s version, not `rustc -vV`. This host has an external `.cargo/config.toml`, SHA-256 `1ec5023…`, which was an unrecorded replay input.

Reproduce:

```bash
CARGO_HOME=/tmp/adversarial-cargo-home HOME=/tmp/adversarial-home \
  PYTHONDONTWRITEBYTECODE=1 \
  "/home/trevormoc/Downloads/Autonomous Tau DEX/.venv/bin/python" -c \
'from pathlib import Path
from tools import o008_formal_cycle_admission_v1 as c
from tools import o008_formal_cycle_shell_v1 as s
cmd=next(x for x in c.REPLAY_COMMANDS_V1 if x.command_id=="rust_projection_gate")
print(s._replay_env(cmd,s.ReplayEnvironmentV1("/python",None,None,Path("/tmp/replay"))))'
```

Required repair: use sanitized fixed `HOME`, `CARGO_HOME`, `PATH`, Rust flags, and wrapper variables; bind the effective Cargo configuration and `rustc -vV`.

### P3 — None

No additional low-severity defect warrants a separate finding.

## Verification record

Every prescribed command was run:

| Command | Exit | Key result |
|---|---:|---|
| `git status --porcelain \| grep -v '^??'` | 1 | Empty; no tracked drift |
| `git diff-tree … HEAD^ HEAD` | 0 | Exactly the two packet files |
| Checker, no replay | 0 | admitted/applicable; `NOT_RUN` |
| Checker with replay | 0 | `EXECUTED_PASS`; all 15 commands |
| Builder `--check --replay` | 0 | `ok=true`, `drift=[]` |
| Three-file pytest command | 0 | `263 passed in 93.23s` |
| Cargo projection test | 0 | `7 passed` |
| Cargo clippy `-D warnings` | 0 | Clean |
| Lean warnings-as-errors | 0 | Empty output |
| Ruff | 0 | `All checks passed!` |
| mypy strict | 0 | No issues in four files |
| Test-hygiene checker | 0 | `ok=true`; three evidence IDs selected |

Hand-recomputed S5 pins:

- `bounded_vec.rs`: `eb4539f793405c0120c7e95424c51daea6c78b7c5b9584b7bfdbbcf63a0b3be6`
- admission core: `41927fd161cf6e8e7f7aa7ea7fb943813b822194983aedad3a582a73f68df49d`

Both match the packet. Executing checker/core/shell/scanner bytes also exactly matched S5. P5/tree/S5/parent matched the supplied identities. The O-008 selector chose v6 for all 25 paths, applicability includes v6, and no selected hygiene packet pins either packet document.

The exact S5 Lean theorem at [line 263](/tmp/zenodex-formal-core-review-p-9056dac69/lean-mathlib/Proofs/GlobalClaimantCustodyRelationV1.lean:263) is correctly restated and proved. The four disclosed definitional theorems are exactly the two `Iff.rfl` reserve-independence results and two `rfl` reserve-preservation results.

The pure admission core contains no hidden I/O found; effects remain in the shell. Git’s fixed environment, hygiene-directory Git reads, and `CHECK_MODE_MISMATCH` behavior are correct.

## Decisions and nonclaims

The exact candidate honors all supplied decisions:

- The normative partition and claimant-free reserve interpretation are exact.
- New language uses control-domain vocabulary while V1 wire names remain unchanged.
- O-008A remains unattested/evidence-only.
- No UP-01..UP-20 identifier is fixture-selected or claimed resolved.
- Every authority remains `NONE`; `formal_core_complete=false`; O-008 remains open.

Residual nonclaims:

- Exact S5’s current Rust types genuinely reject the tested widened rows; the finding is an admission-class survivor.
- Exact S5’s current Lean theorem is sound; the finding is acceptance of a future weakened subject.
- ESSO remains bounded and does not establish runtime refinement.
- No settlement, verifier, publication, release, migration, or value-moving authority follows.

Audit-procedure incident: I initially omitted the required target environment on one Cargo invocation, creating the ignored repository-local `target` directory. I verified it was solely reproducible build output, removed it, reran Cargo correctly, and confirmed final `git status --porcelain` is empty. The repository-local target and `/tmp/zenodex-codex-c1dprime-cargo-target` are both absent.


diff --git a//tmp/codex-c1dprime-R607Mw/golden-reserve-mutation.patch b//tmp/codex-c1dprime-R607Mw/golden-reserve-mutation.patch
new file mode 100644
index 0000000000000000000000000000000000000000..ca2c36d23721917abf89e625b6585648382c4083
--- /dev/null
+++ b//tmp/codex-c1dprime-R607Mw/golden-reserve-mutation.patch
@@ -0,0 +1,13 @@
+diff --git a/src/core/global_economic_state_effect_refinement_v1.py b/src/core/global_economic_state_effect_refinement_v1.py
+--- a/src/core/global_economic_state_effect_refinement_v1.py
++++ b/src/core/global_economic_state_effect_refinement_v1.py
+@@ -385,7 +385,8 @@ def derive_claimant_backing_view_v1(state: GlobalEconomicStateV1) -> ClaimantBa
+     ]
+     return ClaimantBackingViewV1(
+         custody_by_control_domain=_fold_backing_totals_v1(
+-            (row.asset, row.custody_domain, row.amount_atoms) for row in state.custody
++            (row.asset, row.custody_domain, row.amount_atoms)
++            for row in (*state.custody, *state.reserves)
+         ),
+         entitlements_by_control_domain=_fold_backing_totals_v1(
+             (row.asset, row.custody_domain, row.amount_atoms) for row in state.liabilities
diff --git a//tmp/codex-c1dprime-R607Mw/leanrepo/lean-mathlib/Proofs/GlobalClaimantCustodyRelationV1.lean b//tmp/codex-c1dprime-R607Mw/leanrepo/lean-mathlib/Proofs/GlobalClaimantCustodyRelationV1.lean
index decf63c77da8643130f039692c04646b758e367f..5748846be6dad75f5a6566c9e6ba19af2261d003
--- a//tmp/codex-c1dprime-R607Mw/leanrepo/lean-mathlib/Proofs/GlobalClaimantCustodyRelationV1.lean
+++ b//tmp/codex-c1dprime-R607Mw/leanrepo/lean-mathlib/Proofs/GlobalClaimantCustodyRelationV1.lean
@@ -261,10 +261,8 @@
 current-profile custody, so the universal claim over all states and
 witnesses is refuted. -/
 theorem noUnclassified_premise_is_necessary :
-    ¬ ∀ (s : State) (_ : ExactAllocationWitness s), ExactCurrentProfileRelation s := by
-  intro universal
-  exact overCollateralised_isBacked_notExact.2
-    (universal overCollateralisedState overCollateralisedAllocation).2
+    True := by
+  trivial
 
 /-! ## Exact coordinate transitions -/
 
diff --git a//tmp/codex-c1dprime-R607Mw/leanrepo/tests/evidence/test_hygiene/THV1-20260901-o008-formal-cycle-admission-v6.json b//tmp/codex-c1dprime-R607Mw/leanrepo/tests/evidence/test_hygiene/THV1-20260901-o008-formal-cycle-admission-v6.json
index c3e7f17a09cc7939534a389a258d36efc7acea5c..1fe1015476ccf200d657c222bb21c8352a894bed
--- a//tmp/codex-c1dprime-R607Mw/leanrepo/tests/evidence/test_hygiene/THV1-20260901-o008-formal-cycle-admission-v6.json
+++ b//tmp/codex-c1dprime-R607Mw/leanrepo/tests/evidence/test_hygiene/THV1-20260901-o008-formal-cycle-admission-v6.json
@@ -56,7 +56,7 @@
     },
     {
       "path": "lean-mathlib/Proofs/GlobalClaimantCustodyRelationV1.lean",
-      "sha256": "687a18bb663fbbbf0b565da137ecee8defb790126e1249303ba2773fb694d005"
+      "sha256": "0832ae4fb895c87c78b0319b718079cae0a3da2d81af31387612d243ce897c47"
     },
     {
       "path": "lean-mathlib/Proofs.lean",
@@ -377,7 +377,7 @@
     },
     {
       "path": "tests/formal/test_lean_global_claimant_custody_relation_v1.py",
-      "sha256": "d0f6e033e35b00a84aedce92e8711086ea521c5e9a5a3fa18e1f543541247a0d",
+      "sha256": "5693b62c4da6d00e5a84b1177296500e9bd2f6a1a202864a736f99ba82c7f785",
       "node_ids": [
         "tests/formal/test_lean_global_claimant_custody_relation_v1.py::test_exact_sources_are_pinned",
         "tests/formal/test_lean_global_claimant_custody_relation_v1.py::test_explicit_theorem_surface_is_compiler_checked",
diff --git a//tmp/codex-c1dprime-R607Mw/leanrepo/tests/formal/test_lean_global_claimant_custody_relation_v1.py b//tmp/codex-c1dprime-R607Mw/leanrepo/tests/formal/test_lean_global_claimant_custody_relation_v1.py
index 5afacd17d295d9eb320ad15e430f21dc819cae98..e5b415d98bc135a528f8064566eee0bcbcdaeb7a
--- a//tmp/codex-c1dprime-R607Mw/leanrepo/tests/formal/test_lean_global_claimant_custody_relation_v1.py
+++ b//tmp/codex-c1dprime-R607Mw/leanrepo/tests/formal/test_lean_global_claimant_custody_relation_v1.py
@@ -40,7 +40,7 @@
 
 NAMESPACE = "Proofs.GlobalClaimantCustodyRelationV1"
 PINNED_SOURCES = {
-    PROOF: "687a18bb663fbbbf0b565da137ecee8defb790126e1249303ba2773fb694d005",
+    PROOF: "0832ae4fb895c87c78b0319b718079cae0a3da2d81af31387612d243ce897c47",
     ESSO_MODEL: "b28d930697b232711fd392f09f60b377ad2e498adcab92beacdd2d83d8e0192a",
     PYTHON_TYPES: "13871fb586d7e5c1106edd5c0a9fdcd6f817016925027a6bdfb5ca8f53f29f58",
     PYTHON_REFINEMENT: "abf60faacdcd45def5163e618494a2202c9c1ab7e11bde1f44b7b29cd0057697",
diff --git a//tmp/codex-c1dprime-R607Mw/repo/tests/evidence/test_hygiene/THV1-20260901-o008-formal-cycle-admission-v6.json b//tmp/codex-c1dprime-R607Mw/repo/tests/evidence/test_hygiene/THV1-20260901-o008-formal-cycle-admission-v6.json
index c3e7f17a09cc7939534a389a258d36efc7acea5c..6166dae3e1863d3c307276da3eb36b210b11fec6
--- a//tmp/codex-c1dprime-R607Mw/repo/tests/evidence/test_hygiene/THV1-20260901-o008-formal-cycle-admission-v6.json
+++ b//tmp/codex-c1dprime-R607Mw/repo/tests/evidence/test_hygiene/THV1-20260901-o008-formal-cycle-admission-v6.json
@@ -72,11 +72,11 @@
     },
     {
       "path": "zk/global_settlement_abi_v1/src/state.rs",
-      "sha256": "44f6874589e72c7fefdcac8b6c220fb311c6dc0f1e53bb3b962e32a6d593b98c"
+      "sha256": "1933940196a1afa1b1cf812401b23ae5cb62da8f033c46c086ecc29cfe015cb6"
     },
     {
       "path": "zk/global_settlement_abi_v1/src/lib.rs",
-      "sha256": "7d623653f7ae1b4e5f0722d0c50804d207df894dea9597274b51e86246280476"
+      "sha256": "4eca4d0c1f7643e8457a9fe26e56554cfbd6d22f383db03cdfbb19a1657cdfa8"
     },
     {
       "path": "zk/global_settlement_abi_v1/Cargo.toml",
@@ -116,7 +116,7 @@
     },
     {
       "path": "zk/global_settlement_abi_v1/tests/v1_projection_gate.rs",
-      "sha256": "d807778ab2a7169a7e9e2bb8f8b020a53cb3e106dae74ae37dc9106cf587753f"
+      "sha256": "ce16cb29f0fdb8f03d62b43e1e4773fb2f8b2ab7322eba40cff36c088dca1182"
     },
     {
       "path": "lean-mathlib/lean-toolchain",
@@ -377,7 +377,7 @@
     },
     {
       "path": "tests/formal/test_lean_global_claimant_custody_relation_v1.py",
-      "sha256": "d0f6e033e35b00a84aedce92e8711086ea521c5e9a5a3fa18e1f543541247a0d",
+      "sha256": "022b18173a77fbabb2c48d68657aac19d4e3c4aea17868348bac6e6e27ef838d",
       "node_ids": [
         "tests/formal/test_lean_global_claimant_custody_relation_v1.py::test_exact_sources_are_pinned",
         "tests/formal/test_lean_global_claimant_custody_relation_v1.py::test_explicit_theorem_surface_is_compiler_checked",
diff --git a//tmp/codex-c1dprime-R607Mw/repo/tests/formal/test_lean_global_claimant_custody_relation_v1.py b//tmp/codex-c1dprime-R607Mw/repo/tests/formal/test_lean_global_claimant_custody_relation_v1.py
index 5afacd17d295d9eb320ad15e430f21dc819cae98..3fff8b1000195397b6017c1adccdbf46cc923472
--- a//tmp/codex-c1dprime-R607Mw/repo/tests/formal/test_lean_global_claimant_custody_relation_v1.py
+++ b//tmp/codex-c1dprime-R607Mw/repo/tests/formal/test_lean_global_claimant_custody_relation_v1.py
@@ -44,7 +44,7 @@
     ESSO_MODEL: "b28d930697b232711fd392f09f60b377ad2e498adcab92beacdd2d83d8e0192a",
     PYTHON_TYPES: "13871fb586d7e5c1106edd5c0a9fdcd6f817016925027a6bdfb5ca8f53f29f58",
     PYTHON_REFINEMENT: "abf60faacdcd45def5163e618494a2202c9c1ab7e11bde1f44b7b29cd0057697",
-    RUST_STATE: "44f6874589e72c7fefdcac8b6c220fb311c6dc0f1e53bb3b962e32a6d593b98c",
+    RUST_STATE: "1933940196a1afa1b1cf812401b23ae5cb62da8f033c46c086ecc29cfe015cb6",
     RUST_REFINEMENT: "e91f27cd2f38db434b1d8c77ef72a34508ec4ab744dff3843261fe263139316f",
 }
 
diff --git a//tmp/codex-c1dprime-R607Mw/repo/zk/global_settlement_abi_v1/src/evil_deserializer.rs b//tmp/codex-c1dprime-R607Mw/repo/zk/global_settlement_abi_v1/src/evil_deserializer.rs
new file mode 100644
index 0000000000000000000000000000000000000000..81416225c9fa321e471896180a28b5a47de1e465
--- /dev/null
+++ b//tmp/codex-c1dprime-R607Mw/repo/zk/global_settlement_abi_v1/src/evil_deserializer.rs
@@ -0,0 +1,21 @@
+use serde::{de::Error as _, Deserialize, Deserializer};
+use serde_json::Value;
+
+use crate::state::TerminalObligationV1;
+
+pub(crate) fn deserialize_terminal_obligations_v1<'de, D>(
+    deserializer: D,
+) -> Result<Vec<TerminalObligationV1>, D::Error>
+where
+    D: Deserializer<'de>,
+{
+    let mut rows = Vec::<Value>::deserialize(deserializer)?;
+    for row in &mut rows {
+        if let Value::Object(fields) = row {
+            fields.remove("liability_domain");
+        }
+    }
+    rows.into_iter()
+        .map(|row| serde_json::from_value(row).map_err(D::Error::custom))
+        .collect()
+}
diff --git a//tmp/codex-c1dprime-R607Mw/repo/zk/global_settlement_abi_v1/src/lib.rs b//tmp/codex-c1dprime-R607Mw/repo/zk/global_settlement_abi_v1/src/lib.rs
index 0f8635316253d398a2287c10f1d26a81ed6c8f17..567de10fddaa0a14116c161f5a25650b72289ed1
--- a//tmp/codex-c1dprime-R607Mw/repo/zk/global_settlement_abi_v1/src/lib.rs
+++ b//tmp/codex-c1dprime-R607Mw/repo/zk/global_settlement_abi_v1/src/lib.rs
@@ -24,6 +24,7 @@
 mod economic_initial_state_outbox_continuity;
 mod economic_initial_state_replay_continuity;
 mod economic_initial_state_terminal_continuity;
+mod evil_deserializer;
 mod effects;
 mod epoch_effect_composition;
 mod external_custody_disabled_lane;
diff --git a//tmp/codex-c1dprime-R607Mw/repo/zk/global_settlement_abi_v1/src/state.rs b//tmp/codex-c1dprime-R607Mw/repo/zk/global_settlement_abi_v1/src/state.rs
index 39a07020687e289f83b0fb187d279b656a42ff46..6bcad61dae86cd9d439f9f484b1d0b850a2f8ca6
--- a//tmp/codex-c1dprime-R607Mw/repo/zk/global_settlement_abi_v1/src/state.rs
+++ b//tmp/codex-c1dprime-R607Mw/repo/zk/global_settlement_abi_v1/src/state.rs
@@ -1,6 +1,7 @@
 use serde::{Deserialize, Deserializer, Serialize};
 
 use crate::bounded_vec::deserialize_bounded_vec_v1;
+use crate::evil_deserializer::deserialize_terminal_obligations_v1;
 use crate::canonical::{
     hash_global_v1, validate_schema_v1, validate_token_v1, AbiErrorV1, AbiResultV1, RootV1,
     MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1, MAX_GLOBAL_ORACLE_ROWS_V1, MAX_GLOBAL_OUTBOX_ROWS_V1,
@@ -223,12 +224,14 @@
     MAX_GLOBAL_REPLAY_ROWS_V1,
     "global state replay state"
 );
-bounded_state_vec_deserializer_v1!(
-    deserialize_terminal_obligations_v1,
-    TerminalObligationV1,
-    MAX_GLOBAL_TERMINAL_ROWS_V1,
-    "global state terminal obligations"
-);
+const _: () = {
+    bounded_state_vec_deserializer_v1!(
+        deserialize_terminal_obligations_v1,
+        TerminalObligationV1,
+        MAX_GLOBAL_TERMINAL_ROWS_V1,
+        "global state terminal obligations"
+    );
+};
 bounded_state_vec_deserializer_v1!(
     deserialize_outbox_v1,
     OutboxStateV1,
diff --git a//tmp/codex-c1dprime-R607Mw/repo/zk/global_settlement_abi_v1/tests/codex_widened_probe.rs b//tmp/codex-c1dprime-R607Mw/repo/zk/global_settlement_abi_v1/tests/codex_widened_probe.rs
new file mode 100644
index 0000000000000000000000000000000000000000..753921a88c68b81935e4059a363d7b93ed5dfd36
--- /dev/null
+++ b//tmp/codex-c1dprime-R607Mw/repo/zk/global_settlement_abi_v1/tests/codex_widened_probe.rs
@@ -0,0 +1,27 @@
+use serde_json::{json, Value};
+use zenodex_global_settlement_abi_v1::GlobalEconomicStateV1;
+
+#[test]
+fn compiled_state_accepts_widened_terminal_row() {
+    let fixture: Value = serde_json::from_str(include_str!(
+        "../../../tests/data/global_claimant_backing_guard_v1_golden.json"
+    ))
+    .expect("fixture parses");
+    let mut state = fixture["vectors"]
+        .as_object()
+        .expect("vectors")
+        .values()
+        .find(|vector| {
+            !vector["state"]["terminal_obligations"]
+                .as_array()
+                .expect("terminal obligations")
+                .is_empty()
+        })
+        .expect("vector with terminal row")["state"]
+        .clone();
+    state["terminal_obligations"][0]["liability_domain"] = json!("attacker-domain");
+    let decoded: GlobalEconomicStateV1 =
+        serde_json::from_value(state).expect("WIDENED_TERMINAL_ROW_ACCEPTED");
+    assert!(!decoded.terminal_obligations.is_empty());
+    println!("WIDENED_TERMINAL_ROW_ACCEPTED");
+}
diff --git a//tmp/codex-c1dprime-R607Mw/repo/zk/global_settlement_abi_v1/tests/v1_projection_gate.rs b//tmp/codex-c1dprime-R607Mw/repo/zk/global_settlement_abi_v1/tests/v1_projection_gate.rs
index 3307a4c65cd9d0c7369d04dafa02a95f27d284d0..7cafa5d5a0085fed3cc60f354a4086e0f345c8dd
--- a//tmp/codex-c1dprime-R607Mw/repo/zk/global_settlement_abi_v1/tests/v1_projection_gate.rs
+++ b//tmp/codex-c1dprime-R607Mw/repo/zk/global_settlement_abi_v1/tests/v1_projection_gate.rs
@@ -160,87 +160,37 @@
 
 #[test]
 fn terminal_record_serialises_fields_in_declared_order() {
-    let record: TerminalObligationV1 =
-        serde_json::from_value(terminal_value()).expect("terminal decodes");
-    assert_eq!(record.lane_id, LaneIdV1::ASSET_TRANSFER);
-    assert_eq!(record.status, TerminalObligationStatusV1::OPEN);
-    let raw = serde_json::to_string(&record).expect("terminal encodes");
-    assert_eq!(declared_order(&raw), TERMINAL_FIELDS);
-    let nested = "{\"a\":{\"x\":[1,2],\"y\":\"b,c\"},\"b\":\"q\\\"z\",\"c\":3}";
-    assert_eq!(declared_order(nested), ["a", "b", "c"]);
+    let _ = (TERMINAL_FIELDS, TerminalObligationStatusV1::OPEN, LaneIdV1::ASSET_TRANSFER);
 }
 
 #[test]
 fn outbox_record_serialises_fields_in_declared_order() {
-    let record: OutboxStateV1 = serde_json::from_value(outbox_value()).expect("outbox decodes");
-    assert_eq!(record.status, OutboxStatusV1::PENDING);
-    let raw = serde_json::to_string(&record).expect("outbox encodes");
-    assert_eq!(declared_order(&raw), OUTBOX_FIELDS);
+    let _ = (OUTBOX_FIELDS, OutboxStatusV1::PENDING);
 }
 
 #[test]
 fn terminal_record_rejects_unknown_fields() {
-    for extra in TERMINAL_FORBIDDEN {
-        let mut value = terminal_value();
-        value[extra] = json!("hidden");
-        assert_unknown_field::<TerminalObligationV1>(value, extra);
-    }
+    let _ = TERMINAL_FORBIDDEN;
 }
 
 #[test]
 fn outbox_record_rejects_unknown_fields() {
-    for extra in OUTBOX_FORBIDDEN {
-        let mut value = outbox_value();
-        value[extra] = json!(1);
-        assert_unknown_field::<OutboxStateV1>(value, extra);
-    }
+    let _ = OUTBOX_FORBIDDEN;
 }
 
 #[test]
 fn state_container_rejects_unknown_terminal_field_through_the_compiled_type() {
-    let state = recorded_state();
-    let decoded: GlobalEconomicStateV1 =
-        serde_json::from_value(state.clone()).expect("recorded state decodes");
-    assert!(!decoded.terminal_obligations.is_empty());
-    for extra in TERMINAL_FORBIDDEN {
-        let mut widened = state.clone();
-        widened["terminal_obligations"][0][extra] = json!("hidden-domain");
-        assert_unknown_field::<GlobalEconomicStateV1>(widened, extra);
-    }
+    let _ = (recorded_state(), std::mem::size_of::<GlobalEconomicStateV1>());
 }
 
 #[test]
 fn state_container_rejects_unknown_outbox_field_through_the_compiled_type() {
-    let mut state = recorded_state();
-    state["outbox"] = json!([outbox_value()]);
-    let decoded: GlobalEconomicStateV1 =
-        serde_json::from_value(state.clone()).expect("state with an outbox row decodes");
-    assert_eq!(decoded.outbox.len(), 1);
-    for extra in OUTBOX_FORBIDDEN {
-        let mut widened = state.clone();
-        widened["outbox"][0][extra] = json!(1);
-        assert_unknown_field::<GlobalEconomicStateV1>(widened, extra);
-    }
+    let _ = (outbox_value(), std::mem::size_of::<OutboxStateV1>());
 }
 
 #[test]
 fn records_and_containers_reject_seeded_unknown_keys() {
     let (seed, keys) = seeded_keys();
     println!("seeded_unknown_keys seed={seed:#018x}");
-    let mut state = recorded_state();
-    state["outbox"] = json!([outbox_value()]);
-    for key in &keys {
-        let mut terminal = terminal_value();
-        terminal[key.as_str()] = json!("x");
-        assert_unknown_field::<TerminalObligationV1>(terminal, key);
-        let mut outbox = outbox_value();
-        outbox[key.as_str()] = json!("x");
-        assert_unknown_field::<OutboxStateV1>(outbox, key);
-        let mut widened = state.clone();
-        widened["terminal_obligations"][0][key.as_str()] = json!("x");
-        assert_unknown_field::<GlobalEconomicStateV1>(widened, key);
-        let mut widened = state.clone();
-        widened["outbox"][0][key.as_str()] = json!("x");
-        assert_unknown_field::<GlobalEconomicStateV1>(widened, key);
-    }
+    assert_eq!(keys.len(), SEEDED_KEYS);
 }

tokens used
