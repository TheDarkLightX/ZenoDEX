# FCIS M6-R01 OwnedSettlementV2 Revision 3 focused review packet

Review the claim-erased replay and paired-occurrence correction at exact target
commit:

```text
1b3e7d773438705f7b61b34f4f234676e18d3f0d
```

Target tree:

```text
f8dbe8db82df97ab1e4baded63fa45a0fabba0af
```

Target parent:

```text
d6cd7e02e04b4721d993056bb95d68ab0dac1db9
```

The target is design-only and unmounted. It adds no V2 settlement carrier,
claim-erased replay implementation, state-bound configuration, controlled
occurrence, witness batch, normalizer, allocator, transition, receipt, bundle,
proof input, publication path, datastore integration, or runtime mount.

Start with:

```text
REVIEW_PROMPT.md
docs/research/FCIS_M6_R01_OWNED_SETTLEMENT_V2_WITNESS_LANGUAGE_REVISION_3_20260731.md
docs/research/FCIS_M6_R01_OWNED_SETTLEMENT_V2_ATDD_MATRIX_REVISION_3_20260731.json
```

Use only files declared in `SOURCE_MANIFEST.sha256` for the initial review.
Additional repository inspection is allowed when a concrete finding requires
following a named source, consumer, schema, or authority path. Record every
additional path.

Verify:

```bash
sha256sum -c \
  docs/research/prompts/fcis_m6_r01_owned_settlement_v2_revision3_review_v1/SOURCE_MANIFEST.sha256

git rev-parse 1b3e7d773438705f7b61b34f4f234676e18d3f0d^{tree}

git diff --name-status \
  d6cd7e02e04b4721d993056bb95d68ab0dac1db9..1b3e7d773438705f7b61b34f4f234676e18d3f0d

python3 -B -m tools.check_fcis_m6_r01_owned_settlement_v2_revision3_contract

python3 -m pytest -q \
  tests/tools/test_check_fcis_m6_r01_owned_settlement_v2_revision3_contract.py \
  tests/tools/test_check_fcis_m6_r01_owned_settlement_v2_revision3_contract_closure.py \
  tests/tools/test_check_fcis_m6_r01_owned_settlement_v2_revision2_contract.py \
  tests/tools/test_check_fcis_m6_r01_owned_settlement_v2_contract.py \
  tests/core/test_fcis_provisional_fee_replay_v2.py \
  tests/core/test_fcis_fee_occurrence_normal_form.py \
  tests/core/test_fcis_lineage_closure.py \
  tests/core/test_fcis_fee_distribution_configuration.py \
  tests/core/test_fcis_fee_distribution_configuration_admission.py \
  tests/core/test_fcis_fee_distribution_configuration_golden.py \
  tests/tools/test_check_fcis_b1b_revision34_contract.py
```

Expected local evidence:

```text
Revision 3 mutation suite: 87 passed
complete bounded regression selection: 271 passed
```

Return exactly one verdict:

```text
APPROVE_M6_R01_OWNED_SETTLEMENT_V2_REVISION_3_UNMOUNTED
REVISE_M6_R01_OWNED_SETTLEMENT_V2_REVISION_3
NO_GO
```

Approval permits only the next review-bounded settlement carrier, claim-erased
projection, schema, codec, full-root, and vector checkpoint. It does not
approve state-bound configuration, controlled occurrences, witness batches,
normalization, allocation, committed V2 state, transitions, receipts, bundles,
proof inputs, publication, datastore integration, migration, or mounting.
