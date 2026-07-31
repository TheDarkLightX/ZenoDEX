# FCIS M6-R01 OwnedSettlementV2 Revision 2 focused review packet

Review the state-bound, sparse-ordinal witness-language correction at exact
target commit:

```text
16db3da7e3a6ee2716fac260f3de21b47bfd4827
```

Target tree:

```text
8c7a830e9c5e3cacf3431c6b06d432ffbe195302
```

Target parent:

```text
53beba00217274ec9357c3cf42fd11fa2501d306
```

The target is design-only and unmounted. It adds no V2 settlement carrier,
state-bound configuration, controlled witness batch, occurrence-ID authority,
normalizer, allocator, state transition, receipt, bundle, proof input,
publication path, datastore integration, or runtime mount.

Start with:

```text
REVIEW_PROMPT.md
docs/research/FCIS_M6_R01_OWNED_SETTLEMENT_V2_WITNESS_LANGUAGE_REVISION_2_20260731.md
docs/research/FCIS_M6_R01_OWNED_SETTLEMENT_V2_ATDD_MATRIX_REVISION_2_20260731.json
```

Use only files declared in `SOURCE_MANIFEST.sha256` for the initial review.
Additional repository inspection is allowed only when a concrete finding
requires following a named source, consumer, schema, or authority path. Record
every additional path.

Verify:

```bash
sha256sum -c \
  docs/research/prompts/fcis_m6_r01_owned_settlement_v2_revision2_review_v1/SOURCE_MANIFEST.sha256

git rev-parse 16db3da7e3a6ee2716fac260f3de21b47bfd4827^{tree}

git diff --name-status \
  53beba00217274ec9357c3cf42fd11fa2501d306..16db3da7e3a6ee2716fac260f3de21b47bfd4827

python3 -B -m tools.check_fcis_m6_r01_owned_settlement_v2_revision2_contract

python3 -m pytest -q \
  tests/tools/test_check_fcis_m6_r01_owned_settlement_v2_revision2_contract.py \
  tests/tools/test_check_fcis_m6_r01_owned_settlement_v2_contract.py \
  tests/core/test_fcis_provisional_fee_replay_v2.py \
  tests/core/test_fcis_fee_occurrence_normal_form.py \
  tests/core/test_fcis_lineage_closure.py \
  tests/core/test_fcis_fee_distribution_configuration.py \
  tests/core/test_fcis_fee_distribution_configuration_admission.py \
  tests/core/test_fcis_fee_distribution_configuration_golden.py
```

Return exactly one verdict:

```text
APPROVE_M6_R01_OWNED_SETTLEMENT_V2_REVISION_2_UNMOUNTED
REVISE_M6_R01_OWNED_SETTLEMENT_V2_REVISION_2
NO_GO
```

Approval permits the next review-bounded carrier checkpoint only. It does not
approve state-bound configuration, a controlled witness batch, occurrence-ID
authority, normalization, allocation, committed V2 state, a transition,
receipt, bundle, proof input, publication, datastore integration, or mounting.
