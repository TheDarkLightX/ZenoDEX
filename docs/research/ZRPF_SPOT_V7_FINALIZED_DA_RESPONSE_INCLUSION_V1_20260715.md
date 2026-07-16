# ZRPF Spot V7 Finalized DA Response Inclusion V1

Date: 2026-07-15

## Scoped result

This slice authenticates one exact sampled-retrievability evidence digest as
included in a finalized ZenoLedger V0 body no later than the signed response
deadline.

```text
authenticated sampled evidence V1
    + exact response and signature-envelope digests
    + canonical inclusion record V1
    + exact ZenoLedger body bytes
    + authenticated checkpoint-finality V3
    -> private finalized digest-inclusion capability V1
```

The ledger record is data only. The private capability exists only after the
adapter recomputes and cross-checks every binding.

## Record carrier

ZenoLedger V0 has a fixed evidence object and no dedicated retrievability
bucket. V1 carries the exact-schema record in:

```text
body.evidence.oracle_packets
```

The adapter accepts exactly one item with schema:

```text
zenodex.zrpf.sampled_response_ledger_inclusion_record.v1
```

Other oracle packets may coexist within the bounded carrier. A future
ZenoLedger body version should add a dedicated DA-response evidence bucket.
Changing the V0 body key set would change the body ABI and every committed body
root, so that migration is outside this bounded slice.

## Committed fields

The V1 record binds:

- application and application-domain identities;
- ZenoLedger chain identity;
- data epoch, checked epoch, response deadline, and inclusion height;
- sampled policy, certificate, data, and beacon commitments;
- the SHA-256 digest of the exact sampled evidence bytes;
- canonical distinct provider IDs and provider-set root;
- each exact provider-response digest;
- each exact signature-envelope digest;
- the canonical response-record set root.

The adapter additionally binds the exact body root and finalized header hash to
the authenticated checkpoint-finality projection and evidence.

## Timing theorem

For the finalized inclusion height `h`, checked epoch `c`, and response
deadline `d`, acceptance requires:

```text
c <= h <= d
```

Every signed provider response must also declare a response epoch no later than
`h`. The adapter derives `d` from the exact authenticated sampled evidence.
Changing the ledger record to extend the deadline cannot make the capability.

## Explicit non-claims

The slice does not establish:

- that the provider generated or transmitted the response at its declared wall
  time;
- that the sampled evidence bytes themselves were published inside the body;
- public retrieval of the committed data;
- provider administrative or failure-domain independence;
- continuous or future availability;
- erasure-coded reconstruction or data-availability sampling security;
- resistance to hostile code already executing in the same Python interpreter;
- release authority;
- settlement authority;
- production authority.

The exact evidence bytes remain retained by the authenticated sampled-evidence
capability. The body commits their digest and the response/envelope digest set.

## Disaster-state closures

| Disaster state | Closure |
| --- | --- |
| Host extends the deadline in the ledger record | Expected record is regenerated from authenticated evidence and exact comparison rejects |
| Record is inserted after the deadline | Finalized body height must be within the authenticated response window |
| Response and envelope hashes are swapped | Position-distinct response records and root recomposition reject |
| Record is omitted or duplicated | Exact-one schema match rejects |
| Body bytes are substituted | Finalized header/body-root validation rejects |
| Finality application or domain is substituted | Finality projection and evidence cross-binding rejects |
| Raw dictionaries claim verification | Exact private sampled and finality capabilities are required |

## Remaining production work

The next versioned store must persist, in the same atomic transaction:

```text
inclusion record
exact body bytes or durable body resolver identity
finalized header hash and body root
checkpoint-finality certificate and evidence
sampled evidence bytes
response and envelope digest set
```

That store must replay this adapter on open and before every authority-sensitive
read or write. The current slice deliberately stops before the atomic
operational join.
