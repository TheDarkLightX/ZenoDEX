# ZenoLacuna signed project CLI

This document describes the local signed-project command surface. It is an
implementation contract for the supported finite tool. A project revision
is an accepted, replayable finite-model workflow record; it does not grant
settlement, deployment, Tau Net, or human-intent authority.

## Trust boundary

The operator keeps the owner public key pin outside project data and supplies it
with every command that reads or changes a run. The project database never
stores that pin as a source of authority. `prepare` uses it only to reconstruct
the current revision and bind a new parent. An unsigned request cannot be
applied.

The private signing material is a raw 32-byte Ed25519 seed in a user-provided
file with restrictive permissions. `sign` reads that file with `O_NOFOLLOW`,
requires no group or other permission bits, and never prints its contents. The
CLI never generates a key. The operator provisions and protects the key
offline.

The project worker starts in a fresh isolated interpreter with an empty
bytecode-cache prefix. It seals transitive local imports before package
initializers execute and checks their hashes again before emitting success. A source or
checker change therefore requires a fresh process and a new accepted project
history when the checker fingerprint changes.

## Canonical wire objects

All JSON files are bounded and canonical. Objects have no unknown fields,
duplicate keys, floating-point values, or noncanonical encodings.

An unsigned request is the canonical command wire:

```json
{"action":"INIT","parent":null,"payload":"<base64 canonical payload>","project_id":"example","version":1}
```

The payload is a canonical JSON object. Initialization contains `task` and the
current `checker_sha256`. A normal command contains the action-specific fields
below.

| Action | Payload fields created by the convenience builder |
| --- | --- |
| `ANSWER` | `scope_root`, `question`, `answer`, `witness_root` |
| `REVISE` | `scope_root`, `task`, `reason`, `retired_protected` |
| `ASSESS` | `scope_root`, `candidate` |
| `COMPLETE` | `scope_root`, `candidate_root` |
| `CANCEL` / `RESUME` | `scope_root` |

`--payload` accepts a canonical payload file or bounded inline JSON for callers
that already own a typed payload. The command parent defaults to the revision
read from the run. A caller may provide an explicit parent to prepare a request
that is expected to fail as stale; the project transition still checks it.

`sign` converts the request to the existing signed envelope:

```json
{"command":<command wire>,"public_key":"<64 lowercase hex characters>","signature":"<128 lowercase hex characters>","version":1}
```

The signature covers a domain-separated canonical command byte string. The
request and signed envelope are separate artifacts so an agent can propose
data without receiving signing authority.

## Commands

The legacy commands remain available at `tools/zenolacuna.py`. The project
surface is selected by the `project` word:

```bash
python3 tools/zenolacuna.py project task \
  --task TASK.json --adapter relation --out TASK.normalized.json

python3 tools/zenolacuna.py project candidate \
  --mode guarded --out migration-guarded.candidate.json

python3 tools/zenolacuna.py project prepare-init \
  --task TASK.json --project-id example --out INIT.request

python3 tools/zenolacuna.py project sign \
  --request INIT.request --key-file owner.seed --out INIT.signed

python3 tools/zenolacuna.py project apply \
  --run project.sqlite --owner-key OWNER_PUBLIC_KEY --command INIT.signed
```

Legacy `describe` retains its existing profiles and adds a
`project_workflow` descriptor identifying the signed REAL_OWNER path, fresh
source execution, and durable SQLite signed-event evidence.

The remaining commands are:

```text
project prepare       --run DB --owner-key PIN --action ACTION --out REQUEST [action fields]
project candidate     --mode guarded|unguarded --out CANDIDATE.json
project status        --run DB --owner-key PIN
project propose       --run DB --owner-key PIN
project witness       --run DB --owner-key PIN --witness WITNESS.json [--expected-revision REVISION]
project observe       --run DB --owner-key PIN --context NAME --kind ACCEPT|REJECT --observation TEXT [--expected-revision REVISION]
project inspect       --run DB --owner-key PIN --candidate CANDIDATE.json
project export        --run DB --owner-key PIN --out BUNDLE
project replaybundle  --bundle BUNDLE --owner-key PIN [--expected-revision REVISION]
```

`--source-root PATH`, `--tau-bin PATH`, and `--esso-root PATH` select the
explicit host inputs for project reconstruction and runtime completion. They
are accepted on the project command and its subcommands. Missing external
tools, unsupported adapters, source drift, and solver uncertainty remain typed
rejections; a zero exit status is never interpreted as completion by itself.

When `task` receives `--tau-bin`, it records the SHA-256 of that executable in
the task. When it receives `--esso-root`, it records the deterministic
fingerprint of its source, the Z3 package, selected CVC5 executable and Python
interpreter. A later `apply` or `replaybundle` must receive the
same explicit host selection for the corresponding native check. Omitting both
options leaves those checks unrequired. `candidate` emits one of the two
allowlisted signal-migration relation tables as canonical data; it performs no
run or approval operation.

`task --adapter signal-migration` can build the source-pinned fixed migration
task from the selected source root. `task --adapter relation` and
`task --adapter restricted-pipeline` validate or retag an existing task JSON;
their full finite scope is still supplied by that task artifact. A task's
authorization profile is retained unless the operator explicitly selects a
profile. No command silently turns a `SIMULATED` task into an accepted owner
workflow.

Task JSON has the closed shape
`scope`, `runtime`, `delegates`, `tau_sha256`, and `esso_sha256`. Candidate
JSON has the shape below; `candidate` creates the two allowlisted migration
variants without running them:

```json
{
  "allowed": [[0], [0]],
  "assumptions": [0, 1],
  "name": "observed"
}
```

`observe` checks one complete `(context, outcome-kind, observation)` member
against the currently assessed candidate and returns a receipt with the
bounded claim `FINITE_MODEL_MEMBERSHIP`. If `--expected-revision` is omitted,
the CLI reads the latest explicit status revision and the admission method
checks that revision again. The receipt does not authenticate a physical
producer or establish runtime provenance.

`propose` keeps the data-only proposal packet and also exposes its current
`analysis` report, including the distinguishing `witness`, beside the current
`admitted_survivors`. The report is explanatory evidence; it has no approval
authority.

## Startup, restart, and revision handling

Initialization is a signed `INIT` command. `apply` creates the SQLite file
exclusively for that command and commits the event and source snapshots in one
transaction. On startup or after a process restart, `status`, `prepare`, and
all read or apply commands reconstruct the state from the signed event history,
revalidate source bytes, and re-run completion evidence where applicable.

Every successor command names its exact parent revision and scope root. A
prepared request made before another accepted command is stale and cannot
replace the newer state. An exact retry of an already committed signed command
is idempotent; a different command with the same old parent is rejected. A
successful `CANCEL` remains visible in history and requires a new signed
`RESUME` command. `export` writes a complete replay bundle, and
`replaybundle` verifies that bundle without restoring it over a live project.

After source files change, ordinary `status` fails closed with
`SOURCE_DRIFT`. `prepare --action revise` uses the authenticated historical
revision for its read-only payload construction, so an operator can prepare a
successor that names the edited task. Applying that signed revision performs
the normal current-source checks and can still reject the change.

Artifact paths are written with exclusive creation. Existing request, signed,
task, or bundle paths are never overwritten. Use a new path for every prepared
revision and preserve the signed artifacts needed for audit and replay.

## Evidence and non-claims

The focused subprocess checks are:

```bash
python3 -m ruff check src/zenolacuna/project_cli.py tools/zenolacuna.py \
  tests/test_zenolacuna_project_cli.py
python3 -m pytest -q tests/test_zenolacuna_project_cli.py
```

These checks cover fresh initialization, offline signing, restart status
reconstruction, a signed answer successor, profile-preserving rejection,
exclusive artifact writes, restrictive key-file handling, native task pinning,
allowlisted candidate generation, finite observation admission, and legacy
command dispatch. They do not
establish hostile-OS race freedom, human intent,
arbitrary Python execution, production readiness, or an external approval
port. The project reports retain `authority=NONE`; the owner pin proves only
the configured cryptographic key relationship under the host premise.
