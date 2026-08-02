# FCIS M6 G01 proof-context values

Status: `IMPLEMENTED_TESTED_RESEARCH_ONLY_UNMOUNTED`

G01 defines one immutable context value containing the exact dimensions that a
proof/verifier boundary must bind:

```text
chain ID
deployment ID
state root
configuration root
protocol version
language/runtime version
verifier implementation ID
verification-key digest
statement/public-input schema ID
algorithm profile ID
history/genesis authority root
authority epoch
not-before epoch
expiry epoch or none
context root
```

All roots are lowercase fixed 32-byte digests. Text fields are bounded UTF-8
without control characters. Epochs are exact u64 values. An expiry is absent or
not earlier than the not-before epoch, and active-epoch checks are inclusive at
both boundaries.

The context root is derived from every field except `context_root` under:

```text
SHA256(domain_sep("zenodex/fcis/m6/g01/proof-context", 1)
       || canonical_json_bytes(all context fields except context_root))
```

## Authority boundary

`G01ProofContextV1` is an immutable value, not a verified witness. Its public
constructor and builder do not authenticate a proof, select a registry entry,
or grant acceptance authority. A later verifier must revalidate the value at
use and bind it to a pinned registry and ANF public inputs. Canonical byte and
cross-runtime parity work belongs to G02.
