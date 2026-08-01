# FCIS M6 K05 bypass mutation matrix

K05 expands the K01 inventory into a deterministic matrix:

```text
15 inventoried entrypoints x 6 bypass mutations = 90 cases
```

The six mutations are:

```text
return success without commit
direct state write
direct outbox write
skip proof context
skip current-root CAS
use legacy writer
```

Each case must be killed by one named invariant:

```text
missing commit evidence
direct state write not at port
outbox requires committed history
ANF witness required
current-root CAS required
legacy publisher rejected
```

The current-root mutation enters the K02 port with a forged expected head and
must receive `STALE_HEAD`. The remaining mutations are rejected at the model
boundary because they lack the required evidence or unique-port edge.

## Evidence boundary

This is a bounded mutation matrix over reviewed entrypoint identities. It is
not a source-to-source mutation runner and does not execute mounted production
callers. The matrix therefore demonstrates the intended invariant closure for
each named surface while K06-K08 remain responsible for real legacy,
deployment, and mounted-runtime evidence.
