# Assurance Glossary

This glossary keeps the public release vocabulary narrow and consistent across
the README, replay notes, and claims registry.

## `release-backed`

Included in the current published formal or public assurance claim for this
tree.

If something is release-backed, the repo intends people to rely on it as part
of the scoped release statement.

## `public replay`

Reproducible from a fresh clone via the shipped replay and checker surface.

Public replay means the repo ships enough manifests, refs, and scripts for an
independent operator to rerun the bounded assurance lane. It does not mean the
artifact is automatically a full authorization guarantee.

## `authorization-complete`

Safe to treat as a public settlement-authorizing guarantee without extra
trusted environment inputs.

A kernel or certificate is not authorization-complete if its settlement action
still depends on environment-supplied winner, payout, fee, or realized-rate
values that are not yet covered by a trusted witness or equivalent public
acceptance lane.

## `disputed`

Intentionally excluded from stronger public authorization claims until the
missing trust boundary is closed.

Disputed artifacts can still be useful as:

- parity/reference objects
- phase/state-transition objects
- bounded replay surfaces
- intermediate evidence while a witness-backed path is being built

## `reference/parity artifact`

Useful for comparison, regression, or generated-ref parity, but not part of the
published formal release guarantee.

## `witness-backed`

An acceptance path where the emitted decision is paired with a replayable
witness or certificate and a small checker that fails closed on drift.

This is the preferred route for turning older advisory or environment-shaped
surfaces into authorization-complete public guarantees.
