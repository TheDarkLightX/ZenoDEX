# Zeno Oracle Authorization Canonical Vectors

Status: executable reference vectors for typed `OracleAuthorization` hashing.

Generate the vectors with:

```bash
python3 tools/build_oracle_authorization_canonical_vectors.py
```

The emitted receipt fixes the canonical encoding version, stable hash outputs
for an ASCII authorization object, a UTF-8 non-ASCII label vector, and the
`value_hash` rule used by runtime consumers. These vectors are intended for
future Rust, WASM, Solidity, and zkVM verifiers so they can match the Python
reference before becoming authoritative.

The rule is the repo-wide canonical JSON primitive in
`src/state/canonical.py`:

- UTF-8 JSON;
- sorted string keys;
- compact separators;
- no floats, NaN, Infinity, non-string object keys, or surrogate code points.

The regression test is:

```bash
python3 -m pytest -q tests/integration/test_oracle_authorization_canonical_vectors.py
```

These vectors do not prove that another verifier is correct. They are a parity
ratchet: any non-Python verifier must match them before it can safely verify
ZenoOracle authorizations.
