# FCIS M6 E02 nonce/nullifier schema

E02 consumes one verifier-derived `E01RequestIdentityV1` and a state-supplied
current sender nonce. The only accepted relation is:

```text
identity.nonce = current_nonce + 1
```

The increment is evaluated inside a bounded u64 domain. `current_nonce` cannot
be the maximum u64 value, and a Boolean is not an integer alias.

The nullifier preimage is the exact closed object:

```text
{
  deployment_config_root,
  sender_id,
  nonce,
  command_family
}
```

Its root is:

```text
SHA256("zenodex/fcis/m6/e02/nullifier-root/v1" || 0x00 || canonical_json(preimage))
```

The derived `E02NullifierV1` retains the E01 request-identity root as
provenance, while the nullifier root itself excludes command bytes and
post-state. This makes one deployment/sender/nonce/family tuple map to one
nullifier and leaves same-nullifier/different-command collision handling to
the E03 datastore uniqueness task.

The nullifier witness is verifier-owned and point-of-use provenance is checked
by an in-memory research registry. The registry is a model boundary, not a
production authentication or persistence mechanism.
