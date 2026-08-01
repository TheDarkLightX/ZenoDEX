# FCIS M6 C02: Entitlement Key Schema V1

Status: TESTED / UNMOUNTED

## Canonical value

EntitlementKeyV1 is the semantic identity of one adaptive global quota
entitlement history. Its exact fields are:

~~~text
fee_distribution_domain_id
asset
semantic_profile_id
fixed_role_order_id
~~~

The semantic profile must equal:

~~~text
adaptive-global-quota-entitlement/three-role/v1
~~~

The fixed role order must equal:

~~~text
fee-occurrence/role-order/buyback-treasury-rewards/v1
~~~

The domain and asset fields are exact bounded strings. Values are retained
without trimming, case folding, Unicode normalization, or other implicit
coercion.

## Canonical codec

The schema envelope is:

~~~json
{"schema":"zenodex/fcis/entitlement/key/v1","value":{"asset":"USDC","fee_distribution_domain_id":"protocol-fees","fixed_role_order_id":"fee-occurrence/role-order/buyback-treasury-rewards/v1","semantic_profile_id":"adaptive-global-quota-entitlement/three-role/v1"}}
~~~

The canonical digest for the protocol-fees/USDC vector is:

~~~text
0x84dcae8df6706df2316393e5cd37c7f02435b5e9e4a7c64279e9090966e7e56c
~~~

## Rotation and omission boundaries

These values are deliberately outside the key:

- buyback destination
- treasury destination
- rewards destination
- custody account
- ordinary policy weights
- representation codec

Changing one excluded dimension leaves the key bytes unchanged because no such
field can be supplied to EntitlementKeyV1. Changing the domain changes both the
value and canonical bytes. A role permutation or semantic-profile substitution
is rejected by the exact-profile checks.

C02 does not authorize a representation migration. C03 owns the root-bound
migration manifest and C04 owns entry transport. The existing
FeeApportionmentKeyV2 remains the B09 arithmetic-candidate key; this C02 value
is additive research infrastructure and is not wired into a caller, datastore,
authority, or value-moving path.
