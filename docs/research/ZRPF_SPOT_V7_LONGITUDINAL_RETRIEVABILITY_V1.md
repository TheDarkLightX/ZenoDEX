# ZRPF Spot V7 Bounded Longitudinal Retrievability V1

Status: bounded implementation and focused CBC tests present; no continuous,
future, release, settlement, or production authority.

## Exact claim

One accepted private capability establishes:

```text
bounded_finite_window_retrievability_verified = true
```

This means that the same exact governed blob and full-blob certificate passed
the Spot V7 full-blob and authenticated sampled-response boundary at every
discrete epoch in one retained, consecutive, bounded window.

The window contains between two and eight observations. Each observation is an
already-sealed `_GovernedSpotV7DataAvailabilityPrerequisiteV2`. The longitudinal
binder does not parse raw provider responses, verify signatures, authenticate
beacons, or reopen full-blob certificates. Those decisions remain owned by the
lower authority boundaries.

## Correct-by-construction path

```text
exact full blob + authenticated sampled responses
    -> governed DA prerequisite V2 at epoch e

exact full blob + authenticated sampled responses
    -> governed DA prerequisite V2 at epoch e + 1

...
    -> exact private tuple, length 2..8
    -> identical governed policy capability
    -> identical blob, certificate, and policy identity
    -> consecutive checked epochs and source checkpoints
    -> distinct checkpoint, beacon, and sampled-evidence identities
    -> private finite-window capability
```

The binder receives only the tuple. It derives policy and content identity from
the retained capabilities. A caller cannot supply an independent policy root,
window root, Boolean verification claim, start epoch, end epoch, or count.

## Stable content identity

All observations must agree exactly on:

```text
application and domain
ZenoLedger chain
original data epoch
certificate root
data root
chunk root
retention-through epoch
exact blob SHA-256
full-blob policy root
sampled policy root
operational-policy provenance root
operational-policy manifest SHA-256
```

All capabilities must retain the identical in-process governed V3 policy
capability. Equal-looking material from independently minted policy objects is
insufficient for this V1 join.

## Temporal and replay rules

For adjacent observations `i` and `i + 1`:

```text
checked_epoch[i + 1] = checked_epoch[i] + 1
source_checkpoint_sequence[i + 1]
    = source_checkpoint_sequence[i] + 1
```

The checked epochs, source checkpoint hashes, beacon commitments, and sampled
evidence digests must be distinct. The resulting projection records the exact
ordered observations and derives:

```text
window_root = H(
  "zrpf_spot_v7_bounded_longitudinal_retrievability_window_v1",
  exact canonical projection
)
```

The capability retains every exact prerequisite and recomputes its projection
before downstream use. Mutation, copying, deep copying, and serialization are
rejected.

## Why the claim is finite

Sampling at every discrete epoch in a bounded interval proves a stronger fact
than one point-in-time response. It does not prove retrievability between those
observations, outside the window, from an arbitrary public client, or at a
future epoch.

The following remain exactly false:

```text
current_operational_policy_release_head_verified
beacon_unpredictability_verified
response_timing_provenance_verified
provider_independence_verified
continuous_availability_verified
public_future_availability_verified
release_authority
settlement_authority
production_authority
```

Provider-signed response epochs remain assertions inside authenticated response
bytes. This profile does not add independent ledger-inclusion timing evidence.
Repeated responses from governed provider identities also do not establish
administrative, infrastructure, or economic independence.

## Bounded resource posture

The maximum of eight observations bounds retained evidence and revalidation
work. Each prerequisite may retain exact blob, sampled-response, and source-
finality evidence. V1 deliberately avoids an unbounded history vector.

A future rolling accumulator can summarize completed finite windows only after
it has a versioned policy, exact append/merge law, replay protection, and an
authority-preserving persistence boundary.

## Focused negative evidence

The test suite rejects:

- singleton and over-limit tuples;
- duplicate, descending, and gapped checked epochs;
- different exact content or certificate identity;
- independently minted policy capabilities;
- reuse of one source checkpoint hash across observations;
- caller mappings, lists, bytes, and Boolean stand-ins;
- capability copying and serialization;
- mutation of the retained projection.

## Integration boundary

This profile is a private DA fact. No V4 operational-store or settlement path
consumes it in this tranche. A future consumer must define its required minimum
window, persist the exact window root and endpoints atomically, and preserve all
stronger availability and application-authority claims as false unless separate
evidence closes them.
