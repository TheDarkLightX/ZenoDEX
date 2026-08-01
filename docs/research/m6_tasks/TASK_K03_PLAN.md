# K03 plan: static reachability and no-bypass checks

Status: implemented and tested for the reviewed M6 protected source slice;
deployment-complete reachability remains open.

## Objective

Enforce the K02 dependency policy with syntax-aware checks that catch direct
side-effect imports, protected-table writes, legacy publisher calls,
authoritative receipt construction, and direct publication-port bypasses.

## Procedure

1. Load the exact K03 policy and protected source paths.
2. Parse every protected Python file with `ast` and reject syntax failures.
3. Tokenize protected Rust files while skipping comments and strings, then
   reject forbidden `use` paths and effect calls.
4. Check the current source set and report the Rust unmounted boundary when no
   M6 Rust publisher is declared.
5. Run deterministic source mutants for each forbidden structural class.
6. Preserve issue path, line, kind, and detail in the checker output.

## Evidence boundary

K03 is a structural research checker. It does not prove dynamic reachability,
complete deployment/build inclusion, credential isolation, protected-table
ownership in a real datastore, or mounted runtime authority. K04-K08 remain
required for those claims.
