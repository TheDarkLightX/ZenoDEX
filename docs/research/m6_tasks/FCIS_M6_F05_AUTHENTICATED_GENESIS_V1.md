# FCIS M6 F05 authenticated genesis

Status: `IMPLEMENTED_TESTED_RESEARCH_ONLY_UNMOUNTED`

F05 makes genesis an explicit committed value. The value binds:

```text
chain ID
deployment ID
initial state root
initial configuration root
initial authority profile ID and root
history schema
proof-context policy ID and root
migration policy ID and root
```

Its `genesis_root` is derived from every listed field under the versioned
domain `zenodex/fcis/m6/f05/authenticated-genesis`. A caller-selected empty
history has no authority merely because it contains zero transition rows.

## Deployment pin relation

The deployment pin carries the expected genesis root and repeats every
genesis dimension that must remain deployment-bound, including the initial
state root, configuration root, authority profile, history schema, proof
policy, and migration policy. Its own `pin_root` is derived from all pin fields
except that root.

The acceptance relation checks exact equality for every governed dimension and
returns either:

```text
F05GenesisAcceptanceV1 | F05GenesisRejectV1
```

The acceptance root binds the genesis root to the pin root. State substitutions,
crossed genesis roots, foreign chain pins, foreign authority profiles, and
forged value roots are rejected in the independent checker and tests.

## Authority boundary

The Python research model permits construction of a genesis value and a pin.
Those constructors produce data, not authority. In a mounted implementation,
the pin must be loaded from deployment-owned configuration and authenticated by
the configuration/release boundary. The F05 acceptance result must be
revalidated at use and must not be treated as the fresh reopen-head token from
F06.

F05 does not implement cryptographic signatures, quorum authentication,
runtime caller ownership, datastore reopen, migration activation, or value
movement.
