# AutoTrader finite signal profile migration

Status: bounded implementation with executable evidence. Authority: `NONE` for
research results.

A developer and their two agent teams maintain the signal producer and
consumer. They need a smaller transport representation while preserving every
metadata field, the original constructor rejection and the registry decision.
The deployed guard retains responsibility for accepting a signal.

V1 remains the default serialization. V2 is an explicit opt-in producer method
and an additional branch in the existing signal parser and bulk loader. Both
versions normalize to the same existing immutable observation and V1 dictionary.

The exact V2 keys are `schema`, `signal_id`, `source_id`, `profile_code`, `tags`.
The schema is `zenodex/autotrader-external-signal/v2`. Identifiers and tags retain
their existing validation. The exact integer profile has these bits:

| Bits | Field | Codes |
| --- | --- | --- |
| 0..1 | source kind | route=0, local=1, attested=2, advisory=3 |
| 2..3 | trust tier | advisory=0, attested=1, verified=2, protocol=3 |
| 4 | freshness | false=0, true=1 |
| 5 | authentication | false=0, true=1 |
| 6 | advisory only | false=0, true=1 |
| 7 | reserved | must be zero |

Boolean and floating point profile codes, values outside 0..255, reserved bits,
extra or missing V2 fields, and malformed identifiers or tags reject. The V2
decoder must still call the original external-signal constructor. Metadata
encodability gives no signal acceptance or execution permission.

The finite semantic input word places source in bits 5..6, trust in bits 3..4,
freshness in bit 2, authentication in bit 1, and advisory-only in bit 0. The
mounted encoder permutes these fields into the wire layout; the mounted decoder
inverts the permutation. Their full byte domain is checked. Inputs 128..255 map
to the rejection sentinel 255 in the finite kernel; the typed public adapter
turns that sentinel into a rejection and never exposes it as an accepted signal.

For every byte x the normative composition is:

```text
decode(encode(x)) = x,   when 0 <= x < 128
decode(encode(x)) = 255, when 128 <= x <= 255
```

For all 128 metadata states, V1 and V2 must have equal normalized fields or
equal constructor error type and message. The finite theorem covers metadata
and reserved bytes; identifiers, tag validation, JSON decoding, wrapper code,
registry binding and downstream effects need their own executable evidence.
No financial amount is projected into this finite domain.

Given an advisory signal and a human-directed swarm, when producer and consumer
adopt V2, the observer receives the identical signal and registry outcome using
fewer serialized bytes. Given an incompatible independent format revision, the
workbench requires coordination before accepting the combined source. Given a
reserved profile or an object declaring the V2 schema while mixing legacy
fields, parsing rejects without creating an observation. V1-shaped objects
retain the inherited permissive handling of extra fields and unknown schema
labels; the migration does not tighten that separate legacy contract.
Given a cancelled rollout, callers retain V1 serialization and can
continue loading both supported versions; no persistent state migration exists.

Evidence must include the pre-edit 128-row baseline, exact mounted source bytes,
all candidate byte tables, native CPython replay, native Tau queries, a cached
centralized baseline, full normalized-field comparison and wire-size/CPU costs.
Include ordinary batch gzip as a size baseline so repeated JSON keys do not
inflate the apparent practical advantage of the compact format.
Compression and compatibility synthesis are distinct measurements. A slower
Tau compile or codec must be reported. New foundational novelty, patent
clearance, Tau Net admission, production deployment and trading improvements
are outside the claim.
