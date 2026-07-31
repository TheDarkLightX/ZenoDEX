# FCIS M6-R01 OwnedSettlementV2 Revision 1 focused review packet

Review the acyclic provisional-fee witness-language correction at exact target
commit:

```text
dd4175ba5649e0c66d9c4af0594e747de8c3eea8
```

Target tree:

```text
f2574e071ec3f19d0f03463ca3462b705a7b5650
```

The target is design-only and unmounted. It adds no V2 settlement carrier,
controlled witness batch, state transition, receipt, bundle, proof input,
publication path, datastore integration, or runtime mount.

Start with:

```text
REVIEW_PROMPT.md
docs/research/FCIS_M6_R01_OWNED_SETTLEMENT_V2_WITNESS_LANGUAGE_REVISION_1_20260731.md
docs/research/FCIS_M6_R01_OWNED_SETTLEMENT_V2_ATDD_MATRIX_20260731.json
```

Use only files declared in `SOURCE_MANIFEST.sha256` for the initial review.
Additional repository inspection is allowed only when a concrete finding
requires following a named source, consumer, schema, or authority path. Record
every additional path.

Verify:

```bash
sha256sum -c \
  docs/research/prompts/fcis_m6_r01_owned_settlement_v2_revision1_review_v1/SOURCE_MANIFEST.sha256

git merge-base --is-ancestor \
  dd4175ba5649e0c66d9c4af0594e747de8c3eea8 HEAD

python3 -B tools/check_fcis_m6_r01_owned_settlement_v2_contract.py

python3 -m pytest -q \
  tests/tools/test_check_fcis_m6_r01_owned_settlement_v2_contract.py \
  tests/core/test_fcis_provisional_fee_replay_v2.py \
  tests/core/test_fcis_fee_occurrence_normal_form.py \
  tests/core/test_fcis_lineage_closure.py \
  tests/core/test_fcis_fee_distribution_configuration.py \
  tests/core/test_fcis_fee_distribution_configuration_golden.py
```

Return exactly one verdict:

```text
APPROVE_M6_R01_OWNED_SETTLEMENT_V2_REVISION_1_UNMOUNTED
REVISE_M6_R01_OWNED_SETTLEMENT_V2_REVISION_1
NO_GO
```

Approval permits the next review-bounded carrier checkpoint only. It does not
approve the controlled witness batch, authenticated command construction,
committed V2 state, configuration authority, transition, receipt, bundle,
proof input, publication, datastore integration, or runtime mount.
