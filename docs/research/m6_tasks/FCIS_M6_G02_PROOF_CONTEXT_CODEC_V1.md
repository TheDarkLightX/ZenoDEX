# FCIS M6 G02 proof-context codec

Status: `IMPLEMENTED_TESTED_RESEARCH_ONLY_UNMOUNTED`

G02 gives the G01 proof-context value one canonical binary representation. The
codec is a fixed sequence of fifteen named fields. Each field name and value is
length-framed with a big-endian u32. The field count is a big-endian u16. The
header contains the fixed magic `FCIS-M6-G02` and codec version `1`.

The field order and tags are frozen:

```text
chain_id                         T
deployment_id                    T
state_root                       R
configuration_root               R
protocol_version                 T
language_runtime_version         T
verifier_implementation_id      T
verification_key_digest          R
statement_schema_id              T
algorithm_profile_id             T
history_genesis_authority_root   R
authority_epoch                  U
not_before_epoch                 U
expires_at_epoch                 O
context_root                     R
```

`T` is bounded UTF-8 text, `R` is a bounded lowercase `0x`-prefixed 32-byte
root text, `U` is an exact big-endian u64, and `O` is either one zero byte for
absence or one byte `0x01` followed by a big-endian u64. The complete payload
has a 64 KiB bound. Unknown versions, unknown or duplicate fields, reordered
fields, wrong tags, malformed frames, trailing bytes, invalid G01 values, and
crossed context roots return typed rejection.

## Two roots with separate meanings

G01's `context_root` is the semantic identity of the proof context. G02's
`codec_root` is the transport identity:

```text
codec_root = SHA256(
    domain_sep("zenodex/fcis/m6/g02/proof-context-codec", 1)
    || u64_be(len(canonical_bytes))
    || canonical_bytes
)
```

The codec never replaces or redefines the G01 semantic root. Decoding first
reconstructs and revalidates the G01 value, then exposes the exact input bytes
and derives the codec root from those bytes.

## Independent parity

The Python implementation and a small Rust harness construct the same payload
from the same tab-separated vector and compare both the complete payload hex
and codec root. The Rust harness is a parity checker for the codec bytes. It
does not authenticate a caller, verify a proof, select a registry entry, or
grant runtime authority.

## Authority boundary

G02 values and byte strings remain caller-supplied data. A caller can construct
bytes that are structurally valid when the fields and roots are internally
consistent. A later verifier must bind the decoded context to a pinned
registry, authenticated public inputs, and an actual proof before acceptance.
G02 does not mount runtime callers, datastores, recovery, migration, effects,
or value movement.
