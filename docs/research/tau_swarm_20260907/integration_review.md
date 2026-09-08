# Opus completion and local acceptance review

Authority: NONE. Scope: the bounded Tau Swarm application, codec, CLI, replay
and documentation. This does not audit the DEX or establish production safety.

The user selected Claude Opus 5 after unsuccessful Fable completion retries.
`claude-opus-5`, Max effort, returned seven complete files in 1,152.303 seconds.
The source packet contained eleven task files, 84,826 bytes, SHA-256
`f0ba2f11bc20bd8e342e47cd9c0954c6c923c30cc442a7724ba1d40b423b9527`.
The request used no model-side tools. No reported test result was accepted as
execution evidence; the parent ran the deterministic checks locally.

Output exceeded one provider message. Complete file entries were recovered
from saved public-text events and the explicit metadata continuation; incomplete
draft text was discarded. An unrequested author email was removed. Provider
thinking, raw event streams and source packets are not included here.

## Findings and dispositions

| Finding | Correction or evidence | Disposition |
| --- | --- | --- |
| Required replay source could be recorded as `absent` | Restore `source_file_missing`; the new missing-source regression failed before repair and now passes | Closed by parent |
| Source drift raised before a failed replay record was saved | Move the final source check inside the failure-record path; retain `status=FAIL`, exact reason and no passing result | Closed by parent; regression failed before repair |
| Encoder admitted values outside the decoder profile | Validate encoded text through the real decoder and require structural equality; 129-operand and noncanonical-term regressions failed before repair | Closed by parent and independent read-only recheck |
| Invalid order or inspection environment could cause unnecessary native work | Opus validates both before constructing the runtime | Accepted; tests check pre-native rejection |
| Unspecified native-record summary selected fields by length | Replace it with explicit index, operation, binary hash and query hash fields | Closed by parent |
| Missing binary test allowed two different exit classes | Require the observed exact invalid-input result, exit 2, with no output directory | Closed by parent |
| Single-agent cofactor allegedly requires an empty-join special case | Existing `join()` already returns Boolean zero; a new native test checks equality with the complete feasible relation | No defect; regression passes |
| Constant codec allegedly accepts Boolean lookalikes | Existing constructor already requires exact `bool`; codec tests cover malformed values | No defect; first-cycle sources preserved |
| CLI report does not authenticate every auxiliary artifact | Document its semantic-input and gate-byte hash scope and unsigned status | Explicit nonclaim; no authority consumer exists |
| Report overclaimed privacy, communication savings and novelty | Remove those claims; correct the Ignatov title and distinguish measured examples, established mathematics and application hypotheses | Closed by parent |

The separate core review covers exact projection, sequential updates, final
cofactors and proposal binding. Its 65-coordinate availability finding was
repaired before the Opus completion request. The reviewer did not independently
review its own exporter implementation; parent native parity and the final
independent relation oracle cover the exporter within the fixed replay cases.

The independent codec reviewer did not edit or run the final combined suite.
The final tested source hashes are in `replay/report.json`; exact commands and
outcomes are in `validation.json`. Later unchanged-source review does not add
new proof authority.

## Verification shape and remaining limits

The codec regressions reach the wire boundary using valid model values, detect
the representability mismatch and observe exact rejection. The replay negatives
observe missing-source rejection and persisted FAIL status; a zero-case fake
runtime is used only for the failure-reporting test and supplies no native
passing evidence. The native projection mutant, original-relation truth tables,
all admitted cross-products and generated gate traces provide separate semantic
oracles. A single-agent regression tests the identity boundary; a 1+64-block
regression tests local versus global parser capacity.

Ruff and scoped MyPy passed. The red-flag scan found no flags in nine source and
tool files. Metrics retained two low-risk shell/oracle shapes: six explicit
arguments for a fixed expected-count check and a helper mirroring the CLI's
balanced-anchor flag. Neither sits on a value-moving or credential path; no
refactor was needed to preserve the named invariants.

Full artifact authentication, Python-to-Lean refinement, general solver
completeness, maximum-volume synthesis, actual agent execution, Tau Net mounting,
legal clearance and real developer productivity remain outside these results.
