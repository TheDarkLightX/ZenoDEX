# FCIS M6 F06 fresh reopen-head authorization

Status: `IMPLEMENTED_TESTED_RESEARCH_ONLY_UNMOUNTED`

F06 consumes a successful F03 canonical reopen and an F05 genesis relation.
It extracts one exact head containing:

```text
genesis root
canonical durable snapshot/layout root
current state root
current authority state root
current authority epoch
deployment/configuration root
external authorization root
```

The head root is derived from every listed field. External evidence must match
the exact head and its activation/expiry window. A verifier adapter must return
exact `True` before a token is issued.

## Fresh use contract

Every operation boundary calls the external verifier again. The closed
operation set is:

```text
commit
ack_publication
migration
```

The token binds the head root and evidence root. At use, F06 reopens the
canonical bytes again, rechecks F05 genesis ancestry, compares the exact head
and evidence, checks the time window, and invokes the verifier adapter. A
changed snapshot, state root, authority root/epoch, deployment root, genesis,
or external authorization root therefore rejects the old token.

The vector campaign records four verifier calls: one at issue and one for each
of the three operation uses.

## Authority boundary

The adapter is an external authority premise for this research model. F06
does not implement the signer, quorum, deployment configuration loader, or
datastore. The Python token constructor is data construction; the official
issue and use relations own the checks and call the verifier at the exact
boundary. F06 does not mount a production value-moving path.
