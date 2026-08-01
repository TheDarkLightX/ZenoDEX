# FCIS M6 C01: Semantic Profile and Representation Schema V1

Status: `IMPLEMENTED` / `UNMOUNTED`

This note freezes the identity vocabulary needed by M6-R03. The canonical
Python registry is `src/core/fcis_m6_profile_ids.py`; C01 adds no parallel
registry and does not rename the existing SRGD implementation version.

## Canonical identifiers

| Meaning | Canonical identifier | Registry constant |
| --- | --- | --- |
| semantic entitlement transition | `adaptive-global-quota-entitlement/three-role/v1` | `SEMANTIC_ALLOCATOR_PROFILE_ID_V1` |
| SRGD representation codec | `srgd-deficit/v1` | `SRGD_REPRESENTATION_PROFILE_ID_V1` |
| AGQE representation codec | `agqe-surplus/v1` | `AGQE_REPRESENTATION_PROFILE_ID_V1` |
| fixed role order | `fee-occurrence/role-order/buyback-treasury-rewards/v1` | `FIXED_ROLE_ORDER_ID_V1` |

The semantic profile is one transition identity. SRGD and AGQE are two
representations of that transition, related by the sign involution:

~~~text
phi(d) = -d
phi(phi(d)) = d
phi(SRGD_step(d, event)) = AGQE_step(phi(d), event)
~~~

The representation label identifies the codec and may appear in a codec
header or a root-bound migration manifest. It is not an entitlement identity
field.

## State-identity boundary

The state identity must be invariant under changing only the representation
codec. In particular, renaming SRGD as AGQE, or decoding the same history with
the sign-dual coordinates, cannot initialize a new history at zero.

C01 establishes the vocabulary and the exclusion rule. C02 owns the concrete
key value and will make this boundary executable with the exact fields:

~~~text
fee_distribution_domain_id
asset
semantic_profile_id
fixed_role_order_id
~~~

The representation codec, destinations, custody account, and ordinary policy
weights are excluded from that key. C02 must retain negative rotation mutants
for each excluded dimension.

## Registry and alias discipline

- `SEMANTIC_ALLOCATOR_PROFILE_ID_V1` is the canonical semantic-profile name.
- `SRGD_REPRESENTATION_PROFILE_ID_V1` and
  `AGQE_REPRESENTATION_PROFILE_ID_V1` are distinct codec names.
- The existing `SRGD_ALGORITHM_VERSION_V1` is an implementation profile for
  the current SRGD transition code. It is not a second semantic profile and
  is not substituted into the entitlement key by C01.
- Independent postcondition code may repeat the frozen role-order value as an
  expected constant. That repetition is a verifier cross-check, not a second
  caller-selectable registry or semantic alias.
- All M6 registry values are immutable constants or tuples, and the focused
  tests reject duplicate and aliasing mutations.

## Assurance boundary

The A02 registry tests are executable bounded evidence for exact identifier
values and uniqueness. The Morph sign-duality card supplies the reviewed
relation shape. Neither artifact proves a mounted runtime migration or
authorizes value movement. C03-C07 remain required for canonical migration,
history transport, authority binding, and runtime integration.
