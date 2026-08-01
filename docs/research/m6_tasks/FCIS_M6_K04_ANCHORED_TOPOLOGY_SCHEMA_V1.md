# FCIS M6 K04 anchored topology

K04 derives one topology anchor from:

```text
D05 publisher inventory root
D05 anchored topology root
K01 value-moving entrypoint inventory root
K02 unique port ID
canonically ordered K01 publisher IDs
canonically ordered union of D05 and K01 source paths
```

The configuration pins the expected D05 roots, K01 root, publisher set, unique
port ID, and final K04 root. The builder recomputes D05 and K01 from their
source configurations before accepting the K04 pin. A publisher insertion,
source-set insertion, or upstream-root substitution changes the K04 root; the
checked vector then becomes stale until a reviewed topology update occurs.

## Evidence boundary

K04 establishes a deterministic root relation among reviewed research inputs.
It does not prove that those inputs enumerate all production publishers, prove
deployment reachability, or authorize any caller, datastore, migration, or
value movement. The external D05/K01 roots remain reviewed expectations, and
M6 remains unmounted.
