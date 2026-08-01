# K01 plan: value-moving entrypoint inventory

Status: implemented and tested as a source-bound research inventory;
unmounted and incomplete for production deployment reachability.

## Objective

Create one canonical, machine-readable inventory for every reviewed
value-moving or authority-relevant surface. Bind each row to its caller,
input, touched state/effect, required authenticated-normal-form and unique
commit-port edge, legacy status, reachability evidence, and exact source
paths.

## Procedure

1. Load strict JSON configuration with duplicate-key rejection.
2. Require exact row fields, closed enums, canonical relative paths, exact
   booleans, and bounded text/collection sizes.
3. Require the nine D05 publisher IDs and reject duplicates or omissions.
4. Hash configuration, deployment/build paths, and every declared entrypoint
   source file.
5. Reconstruct the typed inventory and derive its domain-separated root.
6. Re-run the builder, checker, typed tests, formatting, compilation, and
   strict mypy gates.
7. Preserve negative witnesses for omitted required surfaces, inserted
   unreviewed surfaces, source digest substitution, proof-verifier value
   movement, and legacy commit-port bypass.

## Evidence boundary

K01 closes the reviewed source-set inventory relation. It does not perform a
complete deployment/build scan, prove dynamic reachability, prove process or
credential isolation, define the unique production commit capability, seal
legacy writers, or mount FCIS M6 value movement. The explicit coverage notes
are part of the generated payload so these gaps cannot be silently omitted.
