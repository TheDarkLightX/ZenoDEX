# Tau Testnet read observer: implementation and bounded qualification

Date: 2026-09-05. Parent integration subject:
`f4c6d84a2b09f60a48302907d659016d00c5d66b` plus the five source subjects below.
This implements the first three read commands from packet 2 of
[the Tau/ADT review](ZENODEX_TAU_ADT_OPTIMIZATION_REVIEW_20260905.md).
The upstream source subject is
[`0b038824c8583a1a902ef54369d3d0ecf3384cf5`](https://github.com/IDNI/tau-testnet/commit/0b038824c8583a1a902ef54369d3d0ecf3384cf5).
This is a source-pinned compatibility result. No deployed peer or current Tau
Language binary was qualified.

## Delivered behavior and authority

`observe_tau_net_v1(config, request)` acquires one observation through a fresh TCP
socket. Its command enum admits only `gettaustate`, `getaccountstate`, and
`gettxstatus`. It sends `hello version=2`, checks the exact hello syntax, then
sends one canonical read. The returned immutable aggregate retains endpoint
configuration, the reported environment, the canonical request, owned typed
response data, and original response bytes. Its authentication label is always
`UNAUTHENTICATED`.

The functional core performs no IO. The shell has no signing, transaction
submission, ledger, replay, history, outbox, or publication port. Both successful
observations and observation failures leave economic authority unchanged. The
adapter has no production caller in this subject. It is available as a library;
it is not mounted into a ledger or HTTP ingress.

This updates neither a policy nor a ZenoLedger state commitment. Hello syntax,
reported environment, account arithmetic consistency, and reported confirmations
do not authenticate the peer or its claims. `unknown` is a successful status
observation; a remote error is a distinct typed observation; transport or local
decode failures yield typed observation rejection. None denotes economic
rejection or authorizes a balance change. Confirmed status can become queued or
unknown on a later read. There is no automatic retry or sticky finality state.

## Protocol findings and local ceilings

- The TCP `getblocks` handler ignores its arguments and requests all stored
  blocks. The database query includes forks. The offline probe confirms that
  `getblocks 1` returns all three supplied fixture blocks. This command is
  deliberately unsupported until a bounded server-side contract is established.
  The original four-command packet is therefore only partially implemented.
- Account amounts use canonical decimal strings; transaction-status integer
  fields use JSON integers. Booleans, floats, non-finite numbers, negative values,
  duplicate keys, unexpected fields, and subject substitutions are rejected.
- Account available balance is `max(0, chain - outgoing - fees)`. Unconfirmed
  incoming value never increases it. A `self` row exposes its outgoing amount
  while omitting its incoming amount. Each such row implies at least one omitted
  incoming atom, but its exact incoming amount cannot be reconstructed. The
  adapter checks that necessary lower bound and makes no stronger derivation
  claim. Incoming-direction rows may have zero transfer value and a sender fee,
  matching the upstream producer's behavior for other transaction operations.
- Local limits are 1 MiB per response, 128 bytes per hello, 256 pending rows,
  65,536 UTF-8 bytes per text field, unsigned 256-bit numeric values, JSON depth
  32, and 16,384 JSON value nodes. Error details use bounded canonical UTF-8 JSON;
  their numbers also obey this local integer profile. This can reject otherwise
  valid upstream diagnostic data or oversized responses. It never truncates them.
- Configuration accepts numeric IP literals of at most 45 characters, ports
  1–65,535, timeouts 1–60,000 ms, and response ceilings 1 byte–1 MiB. Hostnames and
  IPv6 scope identifiers are unsupported. There is no DNS lookup.
- Each receive requests only remaining frame capacity, and at most 1,024 receive
  fragments are accepted per frame. The earliest LF must terminate CRLF at the
  end of the received buffer. Earlier bare LF and coalesced surplus data reject.
  Searches examine only newly received bytes and the prior trailing byte; they
  do not rescan the accumulated frame. This removes quadratic scanning without
  a claimed throughput benchmark. Data arriving after the consumed frame is not
  authenticated or exhaustively inspected; the socket closes after one read.
- One monotonic deadline controls remaining socket timeouts. Successful results
  are admitted only if decoding also finishes before it. Bounded decoding is not
  preempted mid-parse; this is not a hard real-time execution guarantee.

## Evidence and repaired findings

The first core replay produced **3 failures and 58 passes**. The retained failing
cases identified an uncaught attribute error for an incomplete request object,
an incorrect rejection class for empty JSON, and insufficient self-inflow
consistency checks. All three were repaired.

Terra implemented the transport and its tests. Daybreak independently reviewed
the input and transport boundary. The parent reviewed and repaired integration.
Further retained regressions cover small-frame receive allocation, hello limits,
embedded bare LF, incremental framing across every split of a fixture, request
snapshotting before IO, stage-specific failures, response loss, explicit fresh
retries, and post-decode deadline expiry. Opaque diagnostic serialization no
longer amplifies Unicode into ASCII escapes.

Final focused result: **100 pytest cases passed** (64 core, 36 shell). Core tests
also exhaust an 81-case small accounting domain and permute envelope ordering
and whitespace. The upstream probe passed **14 checks**, executing five exact
hash-checked upstream Python files with offline fixture containers. It covers
rule text, mixed/self transfers, over-reservation, unknown/queued/expired and
reported canonical status, mempool precedence, fork-only lookup, dropped status,
and the ignored `getblocks` limit. It starts no node and issues no network request.

Four source-level semantic mutants were applied only to function copies in an
isolated Python process. Each positive baseline passed and the retained test
failed under its mutant:

| Mutant | Changed expression | Retained killer in the core test module |
|---|---|---|
| `DROP_DUPLICATE_KEY_GUARD` | `_pairs`: replace `key not in result` with `True` | `test_duplicate_envelope_keys_cannot_be_overwritten` |
| `DROP_COMMAND_BINDING` | `_response_body`: replace the command equality with `True` | `test_exact_envelope_and_owned_opaque_remote_error` |
| `CREDIT_UNCONFIRMED_INCOMING` | `_account_arithmetic`: add incoming to available balance | `test_account_fixture_separates_incoming_from_spendable_and_owns_rows` |
| `ALLOW_ZERO_SELF_INFLOW` | `_account_arithmetic`: replace `incoming + self_rows` with `incoming` | `test_pending_self_direction_requires_positive_omitted_inflow` |

The fixed vectors are oracle grade 2. The small-domain reservation computation
and separately executed upstream producer supply bounded grade 3 evidence.
Neither proves that a node reports authentic state. The no-writer import check
is supplemental structural evidence; it does not establish deployment-complete
mediation or secure a compromised process.

Ruff check and format pass. Mypy passes with **both source modules named in the
same invocation**, together with the probe. An earlier worker invocation named
only the shell and tests; this repository's import settings treated the core as
`Any`, hiding five union-narrowing errors. Those errors were repaired and the
combined command replayed. Security red-flag scans found no findings. The
core's large-file metric reflects its collocated immutable record types and
bounded parsers; this was reviewed as a single protocol contract, with focused
tests for its branches. Scanner silence and worker review are advisory.

The production-boundary checker passed its **14 checks** on the parent plus
candidate sources. Its output still reports no M6 production mount and
`BLOCKED_OPEN_COVERAGE`; it does not promote this observer or the whole program.

## Replay commands and source subjects

Run from the integration checkout. `TAU_UPSTREAM_REPO` denotes an existing local
Tau Testnet repository containing the pinned commit; the probe does not fetch it.

```bash
python3 -m pytest -q tests/core/test_tau_net_observation_v1.py tests/integration/test_tau_net_observer_v1.py
python3 -m ruff check src/core/tau_net_observation_v1.py src/integration/tau_net_observer_v1.py tests/core/test_tau_net_observation_v1.py tests/integration/test_tau_net_observer_v1.py tools/experiments/tau_net_read_protocol_probe_v1.py
python3 -m ruff format --check src/core/tau_net_observation_v1.py src/integration/tau_net_observer_v1.py tests/core/test_tau_net_observation_v1.py tests/integration/test_tau_net_observer_v1.py tools/experiments/tau_net_read_protocol_probe_v1.py
python3 -m mypy src/core/tau_net_observation_v1.py src/integration/tau_net_observer_v1.py tools/experiments/tau_net_read_protocol_probe_v1.py
python3 -m tools.experiments.tau_net_read_protocol_probe_v1 --upstream "$TAU_UPSTREAM_REPO"
python3 tools/check_production_boundary.py --json
```

| File | SHA-256 |
|---|---|
| `src/core/tau_net_observation_v1.py` | `688fc0b2991bb278d421cd1975e537c9ea5bcdaf86f56feca61a78a7b0288b80` |
| `src/integration/tau_net_observer_v1.py` | `ae06d2c63fda5ef33174e41ce338c479d5562efe714e894f553fb2bef7058f6b` |
| `tests/core/test_tau_net_observation_v1.py` | `33be0cf4c0e3c44089cf8728e28a8b3d998362b6eb452d0396fdc89a9d1434c9` |
| `tests/integration/test_tau_net_observer_v1.py` | `c22334e9413e8800e04e35c761cf57417ba8f675d9b796f5e1079e14d8db4488` |
| `tools/experiments/tau_net_read_protocol_probe_v1.py` | `c7063950dc8ec748fc2aea744ff3fe7798564362ac52783e17868696fbe4e142` |

## Remaining obligations

Status is `IMPLEMENTED` and `TESTED` for the bounded library, and `UNMOUNTED` for
production. W05 still requires committed ledger snapshots, a read-only store
capability, provenance, isolated agreement/disagreement runs, and demonstrated
observational isolation at the actual mount. This node observer does not close
W05 or any economic lane, formal-core, publication, or release gate.

Future endpoint configuration exposed through untrusted ingress needs explicit
destination authorization. Future authenticated observations need a separate
versioned evidence contract binding network/genesis, state identity, source
authenticity, freshness, and any supported finality claim. Plain TCP and the
hello environment label provide none of these. The legacy client and signing
formats remain historical surfaces outside this change.

Unrun: live-node qualification, current Tau engine/ADT execution, Lean/ESSO/Kani/
RISC0 proofs, full repository mypy, and the full critical quality gate. The local
environment still lacks `pytest_cov`, a prerequisite for that gate; it was not
installed. No remote compute, dependency installation, disk audit/cleanup,
economic migration, or authority activation was performed. Formal-core and full
V3 completion remain open.
