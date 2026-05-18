## Canonical Serialization

Current FIRE object artifacts use canonical JSON bytes with:
- UTF-8 encoding
- sorted keys
- `,` and `:` separators with no extra whitespace
- ASCII-safe emission where possible

Hashing rule shape:

```text
object_hash := sha256(canonical_object_json)
instance_hash := sha256(canonical_instance_json)
cert_hash := sha256(canonical_cert_json)
```

Plain English: semantically identical formatting changes must not alter the canonical bytes, and semantic changes must alter the hash.

The long-term target remains stronger domain-separated hashing, but the current migration slice is pinned to the existing deterministic JSON canonicalization already used by the bridge.
