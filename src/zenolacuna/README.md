# ZenoLacuna

Find the missing requirement.

ZenoLacuna is a local verification tool for a developer and their agent
swarm. Given a finite family of interpretations of a specification, it finds
observable disagreement, chooses a separating question, preserves the recorded
answers, and checks a candidate against the selected contract and protected
requirements. Agents propose interpretations and repairs; deterministic checks
decide which finite claims are supported.

The implementation is a Python library and JSON CLI. The signed `project`
workflow supports owner decisions and delegation, task revisions, durable
runtime evidence, cancellation, recovery and independent bundle replay. Its
first release targets explicit finite relations, restricted integer programs,
and a real finite AutoTrader V1/V2 migration controller.

The
[design and logo](../../docs/research/zenolacuna_design_20260908/README.md),
[release contract](../../docs/research/zenolacuna_design_20260908/release_contract.md),
and [Lean proof notes](../../docs/research/zenolacuna_design_20260908/proof_notes.md)
state the supported claims. The older unprefixed CLI remains an explicitly
`SIMULATED` teaching and regression interface.

The [release evidence](../../docs/research/zenolacuna_design_20260908/release_evidence.md)
records 277 passing tests, native Tau/ESSO qualification, independent review,
the measured comparison and a saved canonical replay bundle.

## Use the signed project workflow

Read the [project CLI guide](../../docs/research/zenolacuna_design_20260908/project_cli.md)
for the input schemas and full commands. From the repository root:

```bash
python3 tools/zenolacuna.py project --help
python3 tools/zenolacuna_qualify.py --out /tmp/zenolacuna-qualification
```

The qualification command drives the public CLI through a real finite adapter
change: witness admission, signed decision, protected requirement revision,
unsafe candidate rejection, guarded candidate verification, persisted evidence
and fresh-process replay. It uses publicly known, ephemeral test credentials.
It does not represent an actual owner's approval to deploy an adapter.

To require native checks in that same saved workflow:

```bash
python3 tools/zenolacuna_qualify.py --out /tmp/zenolacuna-native-qualification \
  --tau-bin "$TAU_BIN" --esso-root "$ESSO_ROOT"
```

Use a Python environment with the repository dependencies and Z3, with CVC5 on
PATH or selected by `CVC5_PATH`. ESSO_ROOT contains the separately installed
`ESSO` Python package. Tau and ESSO are explicit host-selected tools; their pins
become part of the signed task. A required check cannot be silently skipped.

For an actual project, the operator supplies an independently pinned owner
public key. The owner's signing key remains outside the proposal agents' access.
Agents exchange JSON proposals; they cannot choose arbitrary executable imports
or grant themselves decision authority. Owner-issued scope-limited delegation
can authorize an agent to answer questions or request verification.

The CLI runs a fresh isolated Python worker, bypasses timestamp-based bytecode
caches, and binds its transitive local source imports before they execute. The
direct Python library requires immutable installed code throughout the entire
process. Neither interface is a sandbox for hostile same-user processes.

## What the demo does

From the repository root, choose a fresh output directory:

```bash
python3 tools/zenolacuna_demo.py --out /tmp/zenolacuna-example
```

The demo reads the existing eight-bit AutoTrader metadata encoder and decoder.
It constructs eight candidate pairs in memory: the original mapping and seven
paired XOR changes. Each changed pair passes all 128 valid-word self round
trips, but both mixed-version pairings misdecode all 128 words. All pairs also
preserve the numeric sentinel for reserved bytes. This is a deliberate mutation
experiment, not a defect claim about the published adapter.

The five aggregate observations produce two behavior classes and one
compatibility question. The demo generates the following artifacts:

| Artifact | Purpose |
| --- | --- |
| `task.json`, `candidate.json` | Finite compatibility problem and a candidate preserving the existing wire mapping. |
| `swarm_packet.json` | Machine-readable context and proposal boundaries for the developer's agents. |
| `codec_report.json` | Concrete mutation results, disagreement witness, question, and a simulated selected contract. |
| `program_task.json`, `program_candidate.json` | A separate full 256-input contract for the unchanged encoder/decoder pipeline. |
| `queue_report.json` | Exhaustive results for a single-message, two-version queue model, including bad histories and safe actions. |
| `unguarded.yaml`, `preserve_decoding.yaml` | Generated ESSO models; canonical JSON is valid YAML. |
| `summary.json` | Scope identity, implementation source hashes, local timings, and which optional tools ran. |

The demo is reproducible teaching and regression material. It does not submit a
real owner's decision, alter the deployed adapter, or publish to Tau Net.
`summary.json` is written only after all requested demo checks finish. A failed
run may leave diagnostic artifacts in its new directory and returns nonzero.

To include separately installed Tau and ESSO:

```bash
python3 tools/zenolacuna_demo.py --out /tmp/zenolacuna-native-example \
  --tau-bin "$TAU_BIN" --esso
```

Tau checks three finite relation comparisons and projects a queue admission
condition. ESSO invokes the installed Z3/CVC5 verification profile on the unsafe
and guarded queue models. A timeout, malformed verdict, or solver disagreement
cannot count as verification. No Tau binary or source is bundled here.

## Library design

Immutable records carry values; standalone deterministic functions carry domain
behavior. `frozen=True, slots=True` dataclasses have exact tuple members and
constructor validation where required. Freezing a dataclass alone would not
make a contained list or dictionary immutable. Small mathematical relations
remain tuples rather than acquiring another wrapper class.

| Module | Responsibility |
| --- | --- |
| `model.py` | Owned scope, requirements, questions, candidates and diagnostic values. |
| `relations.py` | Protected applicability, complete observation equivalence and witnesses. |
| `questions.py` | Exact filtering and bounded minimax question selection. |
| `engine.py` | Pure analysis and repair assessment. |
| `check.py` | Independent finite cell replay and explicitly scoped closure. |
| `codec.py` | Strict JSON decoding and canonical encoding. |
| `authority.py`, `project_core.py` | Signed approvals, exact-parent transitions and owner revisions. |
| `project.py`, `project_storage.py` | Atomic SQLite history, archived sources and fresh evidence replay. |
| `project_runtime.py`, `project_solvers.py` | Runtime correspondence and required native checks. |
| `signal_migration.py` | Real finite producer/consumer/queue migration controller. |
| `project_execution.py`, `project_cli.py` | Sealed source execution and the public project commands. |
| `shell.py` | Compatible simulated prototype lifecycle. |
| `journal.py`, `filesystem.py` | Journal encoding and bounded filesystem operations. |
| `ports/` | Restricted integer programs, fixed signal fixtures, Tau and ESSO. |
| `proposals.py` | Data-only question proposals and swarm packets. |

JSON mappings stop at the decoder. There is no generic mutable model object,
service locator, automatic agent execution, or plugin import of candidate code.
Reports are diagnostic data with `authority=NONE`; a caller-constructed or
persisted report cannot establish acceptance. The shell reconstructs accepted
decisions and reruns checks instead of loading a saved success badge.

## CLI and replay

```bash
python3 tools/zenolacuna.py describe
python3 tools/zenolacuna.py analyze \
  --task /tmp/zenolacuna-example/task.json --out /tmp/zenolacuna-run
python3 tools/zenolacuna.py status --run /tmp/zenolacuna-run
```

`status` includes the current revision, question text, answer vector, surviving
interpretations and witness. A decision must bind that exact revision, scope,
question and witness. In the simulated profile its actor is `simulated-owner`.
The strict decision schema is the `Decision` record in `model.py`; use
`codec.encode` to serialize owned values. An unknown answer requires a new
model decision; it does not silently eliminate inconvenient interpretations.

```bash
python3 tools/zenolacuna.py answer --run /tmp/zenolacuna-run --decision decision.json
python3 tools/zenolacuna.py assess-repair --run /tmp/zenolacuna-run \
  --candidate /tmp/zenolacuna-example/candidate.json
python3 tools/zenolacuna.py replay --run /tmp/zenolacuna-run
```

`replay` checks the finite relation. If no candidate was assessed, it uses the
selected model relation and says so through its model-only claim. A runtime
correspondence claim requires a runtime port. The separate full-byte example
checks source through the existing restricted interpreter:

```bash
python3 tools/zenolacuna.py check-programs \
  --task /tmp/zenolacuna-example/program_task.json \
  --candidate /tmp/zenolacuna-example/program_candidate.json --bits 8 \
  --program src/kernels/python/external_signal_profile_encode_v2.py \
  --program src/kernels/python/external_signal_profile_decode_v2.py
```

This enumerates all 256 concrete inputs. The observation is the returned
integer, including the value 255 on reserved inputs. It does not assert that
returning 255 caused an application-level rejection event. Known V1/V2 signal
fixtures have a separate port that compares actual accept/reject outcomes.

For a persisted integer-domain task, `check-programs --run RUN
--expected-revision REVISION --bits N --program SOURCE.py` reads the checked
decision history and explicitly assessed candidate from that revision. Obtain
the revision from `assess-repair` or `status`; omit `--task` and `--candidate`
in this mode. The returned JSON includes that revision and the fresh runtime
result. This check is read-only: it creates no runtime certificate in the
journal. A stale revision, absent assessed candidate, cancellation, or source
change cannot return completion. The five-observation compatibility task and
the full-byte integer task are different scopes; use the latter with the
integer-program port.

`cancel` and explicit `resume` preserve local history. Exact retries are
idempotent; conflicting duplicates, stale revisions, unauthorized decisions,
source changes and corrupt pointed records reject. Runs bind the checker
source, so changing the implementation requires a fresh run. The filesystem
profile assumes cooperating local writers and does not isolate hostile code
running as the same operating-system user.

## What is established

Exact minimax selection is bounded to 12 semantic classes and 32 questions,
with explicit positive integer costs and work limits. An independent complete
decision-tree oracle checks small families; an unseparable branch remains
unseparable. The larger representation caps are 256 contexts, 512 outcomes,
65,536 cells, 64 hypotheses and 64 questions. These are admission bounds, not
elapsed-time guarantees.

`COMPLETE_FOR_SCOPE` from the model checker quantifies the declared finite
relations, assumptions, observations and protected requirements. It does not
establish that every relevant interpretation or human intention was supplied.
The omission-family names are metadata, not an exhaustive enumeration of every
possible missing requirement. Bounded histories retain a bound. Generic
finite-state graph closure requires a graph adapter and remains inconclusive;
the particular queue demo has its own complete finite graph check.

Twelve Lean theorems establish faithful finite filtering and the equivalence
between question separation and identification of each initially present
class. They do not prove the Python implementation, minimax cost recurrence,
closure checker, filesystem shell, or completeness of the input model.

The signed workflow mounts key authorization, owner-controlled task evolution,
and persisted runtime evidence. The migration graph has one queued message,
128 metadata words, fixed identifiers/tags and eight declared actions. Its OLD
reader is an explicit schema-capability restriction around the installed real
parser, not a reconstructed historical parser binary. Authentication/freshness
fields are observed inputs; this experiment does not authenticate external
reporters or prove freshness against a live chain.

A general migration service, arbitrary program verification and Tau Net
deployment remain outside this release. No production settlement or universal
correctness claim follows from its finite evidence.

## Local checks

```bash
python3 -m ruff check src/zenolacuna tools/zenolacuna.py tools/zenolacuna_demo.py \
  tests/test_zenolacuna*.py tests/zenolacuna_oracle.py
python3 -m mypy --follow-imports=skip src/zenolacuna tools/zenolacuna.py \
  tools/zenolacuna_demo.py tests/test_zenolacuna*.py tests/zenolacuna_oracle.py
python3 -m pytest -q tests/test_zenolacuna*.py
```

Set `TAU_BIN` to include the optional native Tau test. In the existing pinned
Lean environment, run `lake env lean Proofs/ZenoLacuna.lean` from `lean-mathlib`.
These checks do not replace the repository's production release gates.

## License and provenance

This package is original application code under the repository's MIT license.
It calls a separately installed Tau executable through the existing public
query adapter and redistributes no Tau framework files. The research replay
used Tau source revision `3c24bad9ee4c00c5d677fa465797189671823c01`, executable
SHA-256 `b62c0706f682d305fce461750d2332a473ce1fb0e6e7f45b2bb46e5174d07326`,
and installed license SHA-256
`2b7f7abfabd69a5214781d4b1327f0c559d1d2dabfe579b84afde2a4132c4632`.

Tau has its own usage terms. Its license lists research/educational uses and
specified Tau Net uses, excludes framework redistribution from those grants,
and requires an additional license for uses outside its stated categories.
The research results here are not commercial-use or patent clearance. Consult
the license shipped with the executable and the
[upstream Tau license](https://github.com/IDNI/tau-lang/blob/main/LICENSE.md)
for a deployment decision. No Tau internals were copied or reimplemented.
