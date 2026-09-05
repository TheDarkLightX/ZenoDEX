# Tau, ADT, and current Tau Net optimization review

Date: 2026-09-05. Status: research and bounded observations; no product changes or authority promotion.
Initial ZenoDEX subject: `04f0d32b6b6679aa23da645263ec6575f7872c4e`; concurrent parent work continued afterward.
Applied skills: `algorithm-frontier-design-loop` and `tau-semantic-collaboration`; root guidance, applicable overlays, and `docs/ZENODEX_COMPLETION_PLAN.md` were read.

The strongest opportunities are qualification of the current engine, typed ADT row lowering, and a separate current-protocol observer. The historical adapter does not match current Tau Testnet. The measured nonce rewrite failed the performance gate. None of these findings authorizes publication, settlement, finality, licensing, or novelty claims.

## Exact subjects and capability matrix

“Latest” means the public `main` refs observed on 2026-09-05, rather than a deployed-node or release qualification. Live, read-only `git ls-remote` returned Tau Language [`1c1e58aea7ddec04e48ce11cb0e6ed0cbe2a0d43`](https://github.com/IDNI/tau-lang/commit/1c1e58aea7ddec04e48ce11cb0e6ed0cbe2a0d43) and Tau Testnet [`0b038824c8583a1a902ef54369d3d0ecf3384cf5`](https://github.com/IDNI/tau-testnet/commit/0b038824c8583a1a902ef54369d3d0ecf3384cf5). Their commit indexes showed September 2 and August 24 respectively. Current `VERSION` is `0.7.0-alpha`.

| Surface | Actual local observation | Selected current upstream | Consequence |
|---|---|---|---|
| Tau source and executable | Source checkout `1195b4a629250d284ac33789021263dd0395cfb3`; its executable embeds `401d756b` | Main `1c1e58…` | Source HEAD does not authenticate executable provenance. |
| Default runtime | Stable executable embeds `1d4bd3a6`; explicit binary paths used | September engine not executed | Local timing is not current-engine timing. |
| ADTs | Alias probe did not register an ADT; exit zero alone was misleading | Aliases, named/nested tuples, tuple streams, flattened arguments | Current source capability; local runtime qualification missing. |
| Bitvectors and XOR | Copy at widths 32, 64, 256 passed zero/one/maximum; four-input XOR passed 16 binary cases | Broader typed language surface | Blanket “maximum 32 bits” and “XOR unsupported” claims are false; wide arithmetic remains unqualified. |
| Engine settings/API | Historical runner uses scalar streams and REPL/spec fallback | `-B` off by default; C++ logical API; Python interpreter API | Pin options and interface; do not invent Python solver or compiled-snapshot methods. |
| Tau Net protocol | Historical client assumes response prefixes, old signing bytes and absent RPCs | Versioned envelopes and current command registry | Separate protocol version; no silent wire upgrade. |
| Publication | Completion plan assigns ordering/publication to ZenoLedger | Tau Testnet is alpha without economic finality | Tau supplies only replay-qualified pinned properties. |

Current language settings/API are documented in the [pinned language README](https://raw.githubusercontent.com/IDNI/tau-lang/1c1e58aea7ddec04e48ce11cb0e6ed0cbe2a0d43/README.md); transport and finality limits are in the [pinned Testnet README](https://raw.githubusercontent.com/IDNI/tau-testnet/0b038824c8583a1a902ef54369d3d0ecf3384cf5/README.md).

The executed binaries, relative to the main checkout, were:

| Path | Embedded revision, resolved local Git object | Executable SHA-256 |
|---|---|---|
| `external/tau-lang-bitblasting-prev-eea8fb1f/build-Release/tau` | `1d4bd3a6`, `1d4bd3a6623345ea73a1cd5050753679e10c43b9` | `9807526a09dc428a45623274af96e9d930b1b9d84dd340c6910c31395ac001f5` |
| `external/tau-lang/build-Release/tau` | `401d756b`, `401d756bdc290fdd26af73f56a588bc7a036295e` | `e38912c212d79b10addd71f4812bf0eb96f0255f79350d3aee3922b694985656` |

These hashes bind the observed executable bytes; resolving an embedded revision is not a reproducible-build proof.

## What ADTs and tables actually provide

ADT means **Abstract data types** in Tau's official examples. Aliases retain the underlying type; an alias does not create an opaque authority witness or establish unit separation. Named tuples support nesting and inheritance. Equality expands componentwise, and stream members flatten in declaration order. This improves wiring and reviewability without inherently reducing solver variables. Tuple streams have their own nested textual representation and must not replace canonical ZenoDEX serialization implicitly. Missing members can default to zero in documented circumstances; an output tuple may remain unproduced if its members are never mentioned. An adapter must enforce exact members, cardinality, and emission. See the [ADT example](https://raw.githubusercontent.com/IDNI/tau-lang/1c1e58aea7ddec04e48ce11cb0e6ed0cbe2a0d43/demos/demo_4.1-abstract_data_types.tau).

Whole-tuple arguments are flattened during parsing; definitions require a parameter for each flattened member. Do not assume an arbitrary tuple can be passed as one opaque formal argument. REPL type redefinition and session-sticky stream typing also prevent pooling solely by a friendly spec name. See the [argument example](https://raw.githubusercontent.com/IDNI/tau-lang/1c1e58aea7ddec04e48ce11cb0e6ed0cbe2a0d43/demos/demo_4.4-adts_as_arguments.tau).

No documented general SQL/table, dynamic-array, persistent decision-table, or Python compiled-policy-cache API was established. Three distinct mechanisms matter:

1. The local `sbf` implementation uses Boolean-function BDDs. Values can be functions rather than just zero and one; preserving equality-to-top propositions is essential. Source variable order may affect costs, but no universal ordering improvement or supported external ordering API was established.
2. Current Tau has normalization/predicate caches for expressions without recurrence relations. Support-component factoring is opt-in and groups by stream name, so different times of one stream remain coupled; embedded constants or unsuitable support fall back to monolithic processing. This is source evidence, not an executed speedup. See [current implementation](https://raw.githubusercontent.com/IDNI/tau-lang/1c1e58aea7ddec04e48ce11cb0e6ed0cbe2a0d43/src/boolean_algebras/tau_ba.tmpl.h).
3. Testnet already interns eligible wide identities for **equality-only** evaluation. Zero has ID zero, IDs are node-local, width is fixed for a process, and exhaustion requires a fresh process. Canonical text remains the state/history identity; shrunk text is evaluation-only. Arithmetic, ordering, bit operations and ambiguous uses disqualify shrinking. Reusing IDs in roots or wire data would change semantics. See [`tau_shrink.py`](https://github.com/IDNI/tau-testnet/blob/0b038824c8583a1a902ef54369d3d0ecf3384cf5/tau_shrink.py).

## Bounded optimization result: reject the nonce speed proposal

Probe: `tools/experiments/tau_adt_optimization_probe_v1.py`. It creates temporary specs, emits explicit per-case statuses, and changes no product spec. Exit zero means observations completed, including unsupported/error results. Timings include the existing runner's REPL/spec fallback; an initial three-second budget can trigger its 25-second retry. Shared-host elapsed times are observations.

The exact candidate replaces the repeated final predicate with `(o4 = 1 <-> ((o1 = 1) && (o2 = 1) && (o3 = 1)))`, retaining the component constraints. A 128-assignment propositional miter passed. Eight nonce rows, including wrap and maximum neighbors, matched all four outputs in three runs on the stable executable.

| Metric | Baseline | Exact candidate |
|---|---:|---:|
| Expanded formula bytes | 392 | 306 |
| Elapsed seconds, three runs | 21.368486887, 21.297541181, 20.884001463 | 22.766765879, 22.231209294, 22.974957941 |
| Median seconds | 21.297541181 | 22.766765879 |

The expression became 21.9% smaller and the observed median became 6.9% slower. **Do not adopt it as a performance optimization.** The miter establishes this propositional substitution, not complete temporal or compiler equivalence.

An earlier candidate `o4 = o1 & o2 & o3` was discarded before qualification: it constrains the complete algebra-valued output instead of only whether the output equals one. For example, non-top function `x` in `o1`, with `o2=o3=1` and `o4=0`, distinguishes the relations. Its apparent speed gain is invalid evidence and supports no recommendation. The exact candidate was not replayed on the `401d756b` executable; its baseline probe timed out. Copy/XOR successes do not establish general solver completeness or temporal throughput.

## Current Tau Net adapter contract

Use a separate, explicitly versioned adapter. The actual shell transport is text commands over TCP (default 65432, CRLF framing) or WebSocket (default 65433), with `hello version=1|2` negotiation. The handshake is not authentication. Current envelopes carry status, command and data/error; enforce command matching, closed typed decoding, integer ranges, frame limits and deterministic rejection. Sources: [server](https://github.com/IDNI/tau-testnet/blob/0b038824c8583a1a902ef54369d3d0ecf3384cf5/server.py), [response types](https://github.com/IDNI/tau-testnet/blob/0b038824c8583a1a902ef54369d3d0ecf3384cf5/api_response.py).

The first packet should observe `gettaustate`, `getaccountstate`, `gettxstatus`, and bounded `getblocks` responses. The registry supplies no `getappstate`, `getstateproof`, or `apply_app_tx`; no pagination contract was established. `gettaustate` returns rule text, not an authenticated state proof. `checktx` explicitly skips Tau evaluation and reports `tau_evaluated:false`; its success cannot authorize a policy claim. See [`gettaustate`](https://github.com/IDNI/tau-testnet/blob/0b038824c8583a1a902ef54369d3d0ecf3384cf5/commands/gettaustate.py), [`checktx`](https://github.com/IDNI/tau-testnet/blob/0b038824c8583a1a902ef54369d3d0ecf3384cf5/commands/checktx.py).

Pure core: immutable observations, exact decoders, transaction-status transitions and typed rejects. Imperative shell: transport, bounded IO, isolated interpreter lifecycle and persistence. An independently authenticated context must bind the selected network/genesis, block occurrence, policy revision, verifier/runtime profile, freshness, replay scope and canonical transcript. RPC metadata alone cannot construct that witness. Keep SHADOW observations separate from economic state and require the existing ZenoLedger commit gate for publication.

`queued`, `confirmed`, `expired`, `evicted`, `rejected`, and `unknown` are observations; confirmed transactions can reorg back to queued. Unknown is not rejection, and confirmation count is not finality. Preserve response-loss uncertainty and re-query identity before any future retry policy. The completed economic commit's exact retry must retain its original identity. See [`gettxstatus`](https://github.com/IDNI/tau-testnet/blob/0b038824c8583a1a902ef54369d3d0ecf3384cf5/commands/gettxstatus.py).

Future write support must preserve the current six-field canonical signing preimage: sender key, sequence, expiration, fee limit, transaction type and operations. The historical client omits `tx_type`. No explicit network/genesis field is present in that preimage; adding one requires an approved protocol version. Reserved streams are conditional, so “13 and above are safe” is wrong. Current transfer rules use 24-bit amounts even though wider language values exist. See [`sendtx`](https://github.com/IDNI/tau-testnet/blob/0b038824c8583a1a902ef54369d3d0ecf3384cf5/commands/sendtx.py) and [`tau_defs`](https://github.com/IDNI/tau-testnet/blob/0b038824c8583a1a902ef54369d3d0ecf3384cf5/tau_defs.py).

Current rule offers build one total composite per shared output, with sorted acceptors and a neutral default; independently appending implications can lose totality. Preserve the canonical renderer. Native execution is stateful and serialized, so pooled interpreters require lifecycle isolation. See [rule offers](https://github.com/IDNI/tau-testnet/blob/0b038824c8583a1a902ef54369d3d0ecf3384cf5/consensus/rule_offers.py) and [native interface](https://github.com/IDNI/tau-testnet/blob/0b038824c8583a1a902ef54369d3d0ecf3384cf5/tau_native.py).

The current language README says `-F/--max-flag-search-steps` “give-up reports unsat”. Resource-limited UNSAT therefore cannot automatically become a mathematical UNSAT claim. Refuse that mode for negative proof claims unless exhaustion is separately distinguishable; retain timeout/unknown as rejection without proof promotion. `--block-squeeze-cap` instead skips an optimization. These caps have different semantics; generic resource limits are not automatically semantics-preserving optimizations.

## Four bounded next packets, in order

These are proposals with exclusive paths for future work. Thresholds below are selection targets, not achieved benefits. Every packet retains widths, temporal outcomes, fail-closed guards, canonical roots/transcripts and compiler/runtime checks.

| Priority and expected benefit | Exact proposed owned paths | Evidence and acceptance boundary |
|---|---|---|
| 1. Qualify one pinned September runtime and explicit options; expose existing cache improvements and remove version ambiguity. | `tools/experiments/tau_current_runtime_profile_v1.py`; `tests/tau/test_tau_current_runtime_profile_v1.py` | Replay supported contracts with full trace equality, width boundaries, malformed/missing outputs and varied temporal histories. Record executable/build/options hashes. Exhaustion must remain unknown. Adopt a performance profile only after repeatable >=20% median improvement on a declared corpus with no semantic regression. No engine build occurred here. |
| 2. Add a read-only current-protocol observer; resolve known adapter incompatibility without granting authority. | `src/core/tau_net_observation_v1.py`; `src/integration/tau_net_observer_v1.py`; `tests/core/test_tau_net_observation_v1.py`; `tests/integration/test_tau_net_observer_v1.py` | Offline exact upstream fixtures, fragmented/oversized frames, command mismatch, all status transitions, reorg, response loss and malformed numbers. Kill mutants that treat `checktx` as Tau evaluation or confirmations as finality. Assert zero economic/replay/history/outbox mutations for every observation/reject. |
| 3. Lower bounded economic rows to ADTs; reduce manual field wiring and make row completeness testable. | `experiments/tau_adt_rows_v1/row_codec.py`; `experiments/tau_adt_rows_v1/row_contract.tau`; `tests/tau/test_tau_adt_row_codec_v1.py` | Start with 0/1/4/8 rows, complete asset/owner/custody-domain keys, existing integer widths and canonical order. Independently compare scalar and tuple traces; reject missing/extra fields, duplicate keys, wrong widths and absent output. Measure emitted bytes, compile time and memory. No root/wire/schema replacement or claimed solver speedup. |
| 4. Cache immutable preparation artifacts; remove repeated parsing only where identities are complete. | `tools/experiments/tau_preparation_cache_probe_v1.py`; `tests/tau/test_tau_preparation_cache_probe_v1.py` | Key by source bytes, engine/parser/options, typed ABI and policy revision; include initial history/state for any stateful result. Cache prepared syntax before considering verdicts. Test invalidation, eviction, cross-policy/history separation and exact transcripts; measure hit rate, memory and total elapsed time. Reject caching by current row or spec name alone. |

Variable ordering, component factoring and equality-only interning remain secondary experiments after these contracts are established. Source shortening alone did not predict runtime cost. No optimization may truncate identities, replace exact equality with collision-prone hashes, weaken arithmetic guards, merge distinct temporal contexts, or silently alter the current rule renderer.

## Evidence locations, commands and limits

Public-source byte copies and URL/SHA-256 inventories were retained as temporary review evidence in `manifest.json` and `local-git-source-manifest.json`. They are not release artifacts. The first records raw HTTPS downloads; the second records selected already-present Git objects extracted with `git show <commit>:<path>`. The source URLs and content hashes in this report allow retrieval without those temporary files. No Git objects were fetched and no checkout was changed. Parent independently inspected the primary bytes and verified all six downloaded files against the manifest.

Exact raw retrieval used `urllib.request.urlopen(url, timeout=15).read(300000)` for URLs recorded in `manifest.json`, followed by byte writes and SHA-256. Important retained paths relative to the evidence directory:

| Path | SHA-256 |
|---|---|
| `tau-lang/README.md` | `814758073d70f1b38cb97e295c5bcb64f3ef44657d826db300f71becd4d901cd` |
| `tau-lang/VERSION` | `edf28abc4e1068be828235aeda9a1aedd917fe845f1eabf9300c2ea35bd9a521` |
| `tau-lang/demos/demo_4.1-abstract_data_types.tau` | `63b6526a038c67a67616f20d1106ffe7c3ed5b0a734b8d5aba0c2c64f73e9649` |
| `tau-lang/demos/demo_4.4-adts_as_arguments.tau` | `c2cb937d5e314748d216d12f923a8dada5bf7ef234aa6fde6a159cdd13fae95a` |
| `tau-lang/src/boolean_algebras/tau_ba.tmpl.h` | `8440df6ee95b73b220ab608ffc0374a29f47ad96669b9956fbecd7f4a06c3d03` |
| `tau-testnet/README.md` | `5897a1b965096bbb606e0030da84f6beca050518e99428865c95a09f4d34414c` |

Live ref command: `git -c credential.helper= ls-remote --exit-code https://github.com/IDNI/tau-lang.git refs/heads/main`, repeated for `tau-testnet`, with `GIT_CONFIG_NOSYSTEM=1`, `GIT_CONFIG_GLOBAL=/dev/null`, `GIT_TERMINAL_PROMPT=0`, from an isolated scratch directory. Web search/open caches were stale or returned cache misses for some pinned pages; the live refs and raw source bytes are separate evidence. Primary-source reading does not establish executable behavior.

Probe invocation: `python3 -B tools/experiments/tau_adt_optimization_probe_v1.py --tau-bin <explicit-binary> --repeats 3 --timeout-s 3`. The stable three-run exact-candidate observations above bind runner SHA-256 `d2aeba75d26f5b28e7aa01890da4ab2c54678fc8a891c6bdac231a4b7bed3298`, nonce source `231f592b53e567c04951afff0aee5f5d9021a1d6a77ba0d9e68e866f0123a15a`, and candidate `188cfccbe7b919c6058020b0ee8cf6311716579fd7053b60b4327dd9315ff42d`.

Passed after the final `elapsed: list[int]` annotation, including independent parent replay: `python3 -m ruff check tools/experiments/tau_adt_optimization_probe_v1.py`; `python3 -m mypy tools/experiments/tau_adt_optimization_probe_v1.py`. Parent independently replayed the 128-assignment miter and eight nonce cases including wrap rejection. Final probe SHA-256 is `7277b5f42267fe82bfd5a5f4a3027de99077da413e8f1c628f00944bf40e0fd1`. The probe lies under an existing ignored `experiments/` pattern; no ignore rule was edited.

`tools/check_current_tau_compatibility_v1.py` against the available external checkouts returned `REPLAY_CHECKOUT_HEAD_DRIFT` at `current_tau.HEAD`: the Testnet checkout remains historical `f7471ea421d32223b7e48bfecec94b639de9986a`, despite current objects being available for source inspection. This is a failed complete replay, not a passed compatibility gate. The main checkout's six-contract supported-runtime checker was inspected; it is absent from the selected worktree and was not run here.

Unrun: September-engine build/execution, ADT runtime parity, live-node transactions, authenticated snapshot/finality integration, full Tau/TLA/Lean/RISC0 or repository gates. No dependencies, worktrees, disk cleanup, secrets/config reads or product edits were performed. Existing `docs/TAU_ARCHITECTURE.md` and `docs/TAU_LANGUAGE_CONSTRAINTS.md` contain historical capability/performance assertions and require separate source-pinned revision before serving as current optimization guidance. Licensing permission and mathematical novelty remain unestablished.
