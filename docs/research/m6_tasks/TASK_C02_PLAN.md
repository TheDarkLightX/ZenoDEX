# FCIS M6 Task C02 Plan

TASK_ID: C02
TITLE: Freeze entitlement key

## Scope

Create the unmounted R03 entitlement identity value and its canonical codec
without changing the previously tested B09 SRGD key protocol. The new key has
exactly these fields, in this order:

~~~text
fee_distribution_domain_id
asset
semantic_profile_id
fixed_role_order_id
~~~

The semantic and fixed-role fields accept only the C01 registry values. Domain
and asset remain explicit, bounded strings. No representation label is accepted
by the constructor or emitted by the codec.

## Excluded dimensions

The key does not contain:

~~~text
buyback destination
treasury destination
rewards destination
custody account
ordinary policy weights
representation codec
~~~

Destination, custody, policy, and representation rotations therefore produce
the same identity when the four key fields are unchanged. A domain change
produces a different identity; omitting domain from the canonical projection is
a killed mutant.

## Evidence

The focused tests cover exact field order, canonical envelope bytes, stable
digest, semantic/profile rejection, role permutation rejection, unknown
representation input, non-exact field types, domain sensitivity, and excluded
dimensions. The implementation remains unmounted and is reserved for C03-C07
migration and runtime refinement.
