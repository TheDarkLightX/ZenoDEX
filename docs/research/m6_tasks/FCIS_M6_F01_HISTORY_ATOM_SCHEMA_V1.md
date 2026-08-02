# FCIS M6 F01 authoritative history-atom schema

Status: `IMPLEMENTED_TESTED_RESEARCH_ONLY_UNMOUNTED`

F01 defines one immutable transition atom for the later durable-retraction
lane. The atom owns every publication fact that must travel together:

- sequence and commit identity;
- command, predecessor, successor, deployment, verifier, writer, and authority
  roots;
- the complete ANF root;
- an explicit proof-context presence policy and root;
- the E02 sender/command-family/nonce/nullifier projection;
- response, receipt, decision, bundle, and replay roots;
- ordered outbox records with effect and idempotency roots.

The canonical root is:

```text
atomRoot = SHA256(canonical_json_bytes({schema, value}))
```

Every digest is a lowercase `0x`-prefixed 32-byte value. The proof-context
policy is closed. `required` carries a real proof-context root; `not_required`
carries one fixed sentinel root. This removes the ambiguity of an optional
proof-context row.

The nested nullifier rederives the E02 root from deployment, sender, command
family, and nonce. Each outbox record rederives its effect identity from the
owning commit, ordinal, destination, payload root, and writer profile. Its
idempotency root rederives from that effect identity.

The decoder is partial: it returns a complete `F01HistoryAtomV1` or a typed
`F01HistoryAtomRejectV1`. Unknown fields, missing fields, duplicate JSON keys,
noncanonical bytes, wrong enums, malformed roots, crossed rows, and bound
violations do not yield a partial atom.

## Boundary

F01 is a research schema and codec. It does not authenticate a command, mint
runtime authority, verify a proof, publish to a datastore, reopen a database,
prove crash recovery, deliver an external effect, or establish accounting,
backing, zUSD safety, or value movement. F02 owns the canonical history
encoder; F03 owns total reopen and fixed-point recovery.
