# FCIS M6 K06 legacy-seal schema v1

K06 models the build and runtime boundary after the migration reaches
`LEGACY_DISABLED`. The seal binds the complete reviewed inputs needed for this
research slice:

```text
K03 policy root
K03 current scan root
D05 publisher inventory and topology roots
K01 value-moving entrypoint inventory root
J07 authority-switch and post-context roots
target writer profile root
legacy symbol/path sets
unique atomic commit port ID
```

The verifier requires all legacy symbols named by K03 to be present in the
sealed set. The reachable legacy set is exactly empty. The authenticated
feature flag is `legacy_publishers_enabled = false`, and its root covers the
seal policy, D05 topology root, K01 inventory root, and target writer profile.

## Construction and use

`K06LegacySealCertificateV1` has a private verifier construction token. The
checked builder first regenerates K03, D05, and K01 evidence and rechecks the
J07 vector pins. It then mints the certificate and stores a canonical snapshot
for point-of-use verification.

Fresh verification requires:

```text
exact K06 certificate type
certificate field validation
seal root recomputation
verifier-owned object identity
canonical snapshot equality
```

The runtime gate admits only the target writer with the current terminal phase,
authority epoch, topology root, inventory root, disabled feature flag, target
writer ID, and target writer profile. A legacy writer, stale epoch, pre-terminal
phase, crossed root, enabled flag, forged certificate, mutated certificate, or
unknown writer receives a typed rejection.

## Evidence boundary

This is a deterministic functional-core model over reviewed source-bound
inputs. The build gate does not remove legacy symbols from a production image,
authenticate a running process, prove complete call-graph closure, or establish
deployment credential isolation. At the K06 freeze, the older K04 packet was
stale against the current D05 root. The follow-up K04 rebind at
`547901913c2090d19507b8b993f88276ff7f6a62` now passes its current-input gates;
deployment-bound claims remain open for K07.
