# FCIS M6 K03 static no-bypass checker

K03 applies a reviewed policy to the protected M6 core slice with two
syntax-aware scanners:

- Python uses the standard `ast` tree to inspect imports, call targets,
  authoritative constructors, direct port calls, and SQL write literals.
- Rust uses a comment/string-aware token stream to inspect `use` paths and
  effect-call tokens. The current slice has no protected M6 Rust publisher,
  and the report records that fact as `unmounted_no_m6_rust_publisher`.

The policy rejects:

```text
forbidden core imports
direct database/filesystem/network/process/time/random calls
protected-table INSERT/UPDATE/DELETE literals
legacy publisher calls
direct authoritative receipt/bundle constructors outside verifier modules
direct publish_v1 calls outside the unique commit-port module
```

The deterministic mutation campaign checks each class against a synthetic
source witness and also checks the current protected files. A clean scan means
the named source set satisfies the policy. It does not prove that the policy's
source set is complete or that a runtime process reaches it.
