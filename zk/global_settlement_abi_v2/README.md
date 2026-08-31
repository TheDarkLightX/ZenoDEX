# GlobalSettlementABI V2 research mirror

This crate mirrors the research-only Python GlobalSettlementABI V2
asset-transfer functional core and shared O-008 global core. It provides
deterministic typed validation, canonical hashing, a pure asset-transfer
transition, bounded global effect plans, Oracle and terminal lifecycle plans,
all 12 lane-state commitments, bounded global economic state, and exact
state/effect/replay/lifecycle refinement. Python/Rust golden vectors bind the
shared canonical bytes and roots.

It does not mount a runtime route, verify a RISC0 receipt, authenticate the
policy snapshot, implement migration or publisher admission, or grant
settlement or publication authority. Managed issue/burn is outside this
crate's current parity scope. Its production authority is `NONE`.

The closed decoder caps raw canonical input at 1,048,576 bytes. Effect plans
also share the Python per-field, 8,192 aggregate-item, and 1 MiB canonical-byte
ceilings. This crate is not a RISC0 guest or production admission surface.

## Dependency decision

The four direct dependencies are exact-version pinned and the committed lockfile
binds every transitive checksum. `serde` and `serde_json` provide closed-field
typed decoding plus deterministic JSON values, `sha2` implements the existing
Python SHA-256 domain contract, and `hex` renders the fixed root encoding. The
normal dependency graph contains 22 third-party packages and occupies about
16 MiB in the local source cache; build output is disposable and excluded from
Git. These libraries perform no network, filesystem, clock, locale, or random
input. Decoder acceptance still requires exact re-encoding and the crate's own
bounded validators.

The packages declare MIT, Apache-2.0, Unlicense, and Unicode-3.0 combinations;
this records package metadata and grants no legal clearance. An offline locked
build is the required verification mode. The removal alternative is a
repository-local JSON parser, derive replacement, and SHA-256 implementation;
that would enlarge the audited cryptographic and parser surface, so it is
rejected for this bounded mirror.
