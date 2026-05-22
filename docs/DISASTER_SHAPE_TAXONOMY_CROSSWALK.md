# Disaster Shape Taxonomy Crosswalk

This document explains the public-taxonomy crosswalk in
`tools/disaster_shape_taxonomy_crosswalk.json`.

The crosswalk maps public attack and incident families onto ZenoDEX-specific
disaster-search axes. It is a search-expansion tool, not a claim that any public
taxonomy is complete.

The next layer is
[DISASTER_CLASS_CLOSURE_PACKETS.md](DISASTER_CLASS_CLOSURE_PACKETS.md), which
adds explicit bad-trace predicates and theorem obligations for the mapped
families.

## What It Does

The crosswalk answers:

```text
PublicFailureFamily -> one or more ZenoDEX disaster-search axes
```

When a public source names a broad failure family, the crosswalk points to the
local scenario families that should be stressed, replayed, or proved for
ZenoDEX.

Current checked status:

```text
entry_count = 20
public_source_count = 6
source_family_count = 60
known_axis_count = 125
mapped_axis_count = 125
unmapped_axis_count = 0
orphan_mapping_count = 0
```

Every current axis in `DISASTER_SEARCH_EXPANSION_AXES` is mapped to at least one
publicly seeded disaster family.

## What It Does Not Claim

The crosswalk does not prove ZenoDEX is safe against every possible adversarial
shape. It also does not claim CAPEC, OWASP, SWC, Rekt, or chaos-engineering
sources are exhaustive.

The useful claim is narrower:

```text
axis is current ∧ axis is mapped -> axis has at least one public seed family
```

No current disaster-search axis is floating without a public threat-model seed.
The axis still needs its own replay, proof, fuzz, or out-of-scope evidence
before it becomes an assurance claim.

## Public Sources

The current crosswalk uses:

- MITRE CAPEC: https://capec.mitre.org/
- OWASP Smart Contract Security Verification Standard: https://scs.owasp.org/SCSVS/
- OWASP Smart Contract Top 10: https://owasp.org/www-project-smart-contract-top-10/
- Smart Contract Weakness Classification Registry: https://github.com/SmartContractSecurity/SWC-registry
- De.Fi Rekt Database: https://docs.de.fi/audits/rekt-database
- Principles of Chaos Engineering: https://principlesofchaos.org/

The SWC registry is treated as a legacy source because it is no longer actively
maintained. It is useful for historical naming, not as a complete current list.

## Replay

Run the checker:

```bash
python3 tools/check_disaster_shape_taxonomy_crosswalk.py
```

JSON output:

```bash
python3 tools/check_disaster_shape_taxonomy_crosswalk.py --format json
```

The checker imports the live axis list from
`tools.stateful_scenario_bridge.DISASTER_SEARCH_EXPANSION_AXES`, so it fails if:

- the crosswalk maps an axis that no longer exists;
- a current disaster-search axis has no public-family mapping;
- an entry is malformed or duplicates an ID.

## How To Use It

When a new public incident, audit finding, CAPEC pattern, or OWASP weakness
looks relevant:

1. Add or update a crosswalk entry.
2. Map it to existing ZenoDEX axes when possible.
3. If no axis fits, create a new backlog axis in the disaster-search plan.
4. Promote the axis only after it has replayable evidence, proof evidence,
   fuzz evidence, or an explicit out-of-scope decision.

The intended loop is:

```text
public incident -> local axis -> witness or proof lane -> regression receipt
```

External knowledge expands the search space, but repo-local evidence is still
what makes a safety claim credible.
