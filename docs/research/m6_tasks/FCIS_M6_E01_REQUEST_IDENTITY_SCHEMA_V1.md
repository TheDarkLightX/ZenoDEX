# FCIS M6 E01 request identity schema

E01 derives one stable retry identity from a verifier-owned authenticated
command witness and explicit deployment, sequence, and authority context.
The public constructors for the authenticated command and request identity
reject ordinary caller construction. The witness contains command, sender,
family, nonce, authentication-profile, and authentication-evidence roots. The
identity binds the stable authentication profile root and excludes ephemeral
evidence bytes from its retry preimage.

## Canonical identity body

```text
deployment_config_root
authentication_profile_root
sender_id
command_root
command_family
nonce                  u64
expected_sequence      positive u32
authority_epoch_index  u32
```

The body has an exact field set and canonical JSON encoding. Digests are 64
lowercase hexadecimal characters, strings are bounded UTF-8 values, the
command family is a closed enum, and booleans do not cross integer fields.
The request identity root is the domain-separated hash of this body.

## Boundary

The private fixture mint helper stands for an external verifier that has
already authenticated the command. E01 does not implement signatures,
credential verification, commit authorization, datastore mutation, replay
storage, or a mounted caller. M6 remains research-only and non-promotable.
