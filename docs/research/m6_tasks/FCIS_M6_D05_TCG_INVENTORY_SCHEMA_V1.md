# FCIS M6 D05 TCG Publisher Inventory Schema v1

TASK_ID: D05

## Purpose

D05 derives the publisher inventory and its topology anchor from a reviewed
deployment/build configuration plus the exact bytes of every declared source
file. The builder has no runtime certificate input and never accepts a
candidate topology or instance root as an authority source.

The generated payload is research-only evidence for a later TCG boundary. It
does not claim that the selected inventory is complete for the production
repository.

## Configuration

The reviewed configuration is:

```text
config/deploy/fcis_m6_tcg_inventory_v1.json
```

Its exact fields are:

```text
schema
profile_id
deployment_sources[] = {path, purpose}
publishers[] = {
  publisher_id,
  kind,
  entrypoint,
  source_paths[],
  effect_capable,
  authority_sink
}
```

The builder hashes the raw configuration bytes. The configuration path itself
is also included in the source manifest.

## Required publisher kinds

The closed enum contains:

```text
api
cli
administrator
migration_worker
recovery_worker
proof_verifier
legacy_runtime
background_outbox_worker
direct_datastore_adapter
```

Every required kind must occur at least once. Publisher IDs are unique and
canonically ordered. A publisher may reference more than one reviewed source
file. Every referenced path must occur in the derived source manifest.

## Derived source manifest

Each source entry contains:

```text
path
purpose
source_sha256
source_bytes
```

Paths are repository-relative POSIX paths with no traversal components. Source
bytes are read by the imperative builder and converted to typed values before
root derivation. The configuration source, deployment/build sources, and all
publisher sources are included exactly once by path.

## Roots

The publisher inventory root is:

```text
H(
  "zenodex/fcis/m6/d05/tcg-publisher-inventory/v1",
  canonical_inventory_payload
)
```

The anchored topology root is:

```text
H(
  "zenodex/fcis/m6/d05/anchored-topology/v1",
  {
    schema,
    profile_id,
    configuration_path,
    configuration_sha256,
    publisher_inventory_root,
    publisher_ids,
    source_paths
  }
)
```

Both hashes use the repository canonical JSON bytes and a domain separator.
The topology root therefore changes when a publisher is inserted or omitted,
when a source digest changes, or when the reviewed configuration changes.

## Fail-closed rules

The typed core rejects:

- duplicate JSON fields;
- unknown configuration fields;
- unsupported publisher kinds;
- duplicate publisher IDs;
- missing required publisher kinds;
- missing or unanchored source paths;
- noncanonical ordering;
- path traversal, absolute paths, and non-regular files;
- wrong enum, boolean, integer, digest, or collection types;
- empty publisher, source, or sink coverage.

## Boundary

The inventory root is an external expectation for a later TCG verifier. It is
not a proof of deployment completeness, runtime reachability, caller
authentication, datastore authority, migration authority, proof-context
validity, destination behavior, or value movement.
