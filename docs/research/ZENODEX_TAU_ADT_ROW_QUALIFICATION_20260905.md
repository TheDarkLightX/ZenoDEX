# Tau ADT row transport qualification

This is the executable successor to the ADT feasibility section of
[the optimization review](ZENODEX_TAU_ADT_OPTIMIZATION_REVIEW_20260905.md).
The base is V3 integration commit `08905c720c`. It establishes bounded row
transport on one measured Tau executable. It grants no economic, ledger,
receipt-verification, or publication authority.

## Implemented adapter

`experiments/tau_adt_rows_v1/row_codec.py` takes an exact tuple of at most eight
owned `EconomicAmountV2` rows. It snapshots and revalidates each field before
ordering or hashing keys, including malformed instances of the exact class.
Keys are unique and ordered by `(asset, owner, custody_domain)`.

Each complete identity is represented by its ASCII bytes, right-padded with
zero bytes to 160 bytes and encoded as `bv[1280]`. No hash or interned identifier
replaces the string. Decoding rejects internal/leading zero bytes, invalid
ASCII, width overflow and noncanonical decimals. Amounts use `bv[128]` and
retain both zero and `2^128 - 1` as permitted by the owned row constructor.

The identity contract `row_contract.tau` declares the four fields and streams
`o[t] = i[t]`. The decoder accepts only exact banners, ordered output indices,
bounded optional timing lines and the declared row shape. Missing, extra,
duplicate, reordered, malformed or diagnostic output rejects. The caller must
compare decoded rows with its expected snapshot; the decoder receives a count,
not authenticated source authority.

## Measured execution and evidence

The executable reports `Tau Language Framework version 0.7.0-alpha (1c1e58ae)`.
Its measured SHA-256 is
`c061c870b47fa1a6089dac59285e8473b7b789dc600157704007f2d67fd90950`.
That reported version is not proof of correspondence to a rebuilt source tree.

`execution.py` copies the measured ELF into a sealed memfd using the existing
receipt adapter's bounded copy checker, then executes that immutable copy.
It uses nonblocking raw-byte IO, a single 12-second deadline per invocation,
64 KiB stdout and 4 KiB stderr ceilings, and explicit ASCII decoding. CR and
CRLF reject instead of silently becoming LF. The child inherits only
`LC_ALL=C` in its environment. This is not a syscall or network sandbox.

`qualify.py` checks exact contract bytes and snapshots loaded repository source
files before and after execution. The retained run bound 130 repository source
files, including row primitives, canonicalization and the reused execution
helpers. All recorded source hashes matched an independent post-run check.
Python loaded modules, kernel/procfs/memfd behavior, the dynamic loader and
system libraries remain trusted. Source hashes are not process attestation.

Positive controls passed for 0, 1, 4 and 8 rows and a separate maximum-identity
case. Every identity coordinate and amount also passed a scalar Tau replay
against independent positional-integer encoding. This covers five ADT and
twenty scalar invocations.

Missing-field, extra-field and u128-overflow inputs produced the pinned
engine's exact diagnostic tuples and rejected through the adapter. All three
engine exits were zero. The qualification gate requires those exact diagnostics
and normal exit; crashes, nonzero startup failures, missing transcripts and
unrelated text containing `Error` cannot count as successful rejection. The
engine emits ANSI-wrapped error labels even with `--color false`; those exact
bytes are recorded in the scoped negative contract.

The qualification receipt SHA-256 is
`c824b4312a88c3ba9bfd6db380a5ee8972579b07a06c710225f4b9dee5b55a1a`.
Timing lines make fresh transcript/receipt hashes vary; semantic acceptance,
input hashes and source bindings remain checked on each replay.

| Source | SHA-256 |
| --- | --- |
| `row_codec.py` | `60754e4cf32e404fb8988e6e8c5abeb96c696a880daec9d5c8d0d32d624eb6a7` |
| `row_contract.tau` | `01eb6351bf20045224767a118cd7745caabbe21e776ea93a0b8d45c272bbeb48` |
| `execution.py` | `c9bd254baaa258a0eecaa5d8600e3202d84a5b4360707b0a45236cd1373ab7ec` |
| `qualify.py` | `858b91540fb055a99a64e910dfa7b8b2caf013146ba173caf37c40e6fa3d1d3c` |

## Performance interpretation

The final eight-row probe emitted 10,232 stdout bytes from 9,867 input bytes.
Its one ADT process took approximately 5.38 seconds; four scalar processes
took approximately 2.39 seconds together. This was one contended run, not a
benchmark campaign, and does not establish a general speed ratio. Full-width
ADT transport has not demonstrated a speed improvement over this scalar
baseline. Peak memory was not measured.

ADT representation is useful for retaining a row's related coordinates.
Optimization should next compare actual economic predicates under identical
semantics and resource limits. Shrinking an identity to an unauthenticated
number or omitting a field would lose the property established here.

## Review and replay

Luna implemented the codec. Parent review added canonical timestep and forged
row regressions plus an independent packing oracle. Independent defensive
review identified and closed executable pathname races, unbounded output,
newline normalization, incomplete source binding, stale successful output
reports and ambiguous negative-outcome classification. No findings remain in
the reviewed research scope.

From the repository root, set `TAU_BINARY` to the measured executable above:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 -m experiments.tau_adt_rows_v1.qualify \
  --tau-binary "$TAU_BINARY" --output /tmp/zenodex-tau-adt-qualification-v1.json
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider \
  tests/tau/test_tau_adt_row_codec_v1.py \
  tests/tau/test_tau_adt_qualification_v1.py \
  tests/tau/test_tau_adt_execution_v1.py
python3 -m mypy --explicit-package-bases --follow-imports=silent \
  --cache-dir=/dev/null experiments/tau_adt_rows_v1
```

The Tau tests passed 56 cases. They contributed to an 85-case parent run with
the buyback formal/runtime work. Ruff and narrow mypy passed. The existing
production-boundary checker passed 14 checks while maintaining its blocked,
unmounted M6 posture. The local sandbox denied memfd execution; the measured
replay ran outside that sandbox with scoped authorization. No unsealed
executable fallback was introduced.

No full Tau build, remote/GPU run, RISC0 proving, production activation,
economic-predicate qualification, authenticated state retrieval, or full
supported-runtime promotion was performed. The core remains pure, and this
adapter remains outside production callers. It advances the experimental
Tau integration work; W03-W06 and whole-program release obligations remain
separate and open.
