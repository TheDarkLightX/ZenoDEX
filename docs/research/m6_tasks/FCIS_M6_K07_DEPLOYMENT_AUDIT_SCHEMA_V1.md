# FCIS M6 K07 deployment-boundary audit schema v1

K07 binds one deployment audit to:

```text
K04 topology anchor root
K06 terminal legacy-seal root
K01 value-moving entrypoint inventory root
complete K04 audited source-path set
declared deployment-path subset
declared process launch bindings
all source/deployment findings
```

The audit scans Python string literals and SQLite connection calls for direct
protected-table writers, scans deployment files for forbidden plaintext
credential markers, checks required production-policy markers, verifies each
declared launcher command, and checks that inventoried worker source paths are
covered by the anchored audit set. The container testnet-demo branch requires
an explicitly supplied `DEMO_API_TOKEN`; it does not mint a fallback token.

The result has two exact statuses:

```text
PASS  iff findings = ()
GAP   iff findings is nonempty
```

The audit is verifier-owned. A caller cannot construct a valid audit, mutate a
valid audit into a clean result, or use an `object.__new__` copy as deployment
authority. A clean-deployment decision is also minted only by the point-of-use
gate. Current evidence is `GAP`: the H02 SQLite adapter contains direct table
writes. The entrypoint credential-default gap was repaired and remains covered
by a negative scanner witness and a missing-secret startup test.

## Evidence boundary

K07 is a deterministic research audit over the current reviewed source set. It
does not prove complete operating-system process reachability, image contents,
credential isolation, live database ownership, or runtime call-graph closure.
The `GAP` result blocks deployment-bound claims, authority switching, and value
movement.
