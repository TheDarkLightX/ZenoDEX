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

The derived `E02NullifierV1` retains the exact verifier-derived E01 request
identity and the exact current nonce supplied to the E02 relation. Its wire
projection retains the E01 request-identity root, while the nullifier root
itself excludes command bytes and post-state. This makes one
deployment/sender/nonce/family tuple map to one nullifier and leaves
same-nullifier/different-command collision handling to the E03 datastore
uniqueness task.

Every point-of-use verification freshly revalidates the retained E01 identity,
rechecks the exact-next-nonce relation, and recomputes the nullifier root. E02
does not use process-global object identity or an in-memory provenance
registry. The E01 authentication witness remains an explicit external verifier
premise in this research slice.
