# FCIS M6 D03 ANF Receipt Binding Schema V1

Status: TESTED / UNMOUNTED

## Receipt fields

The canonical ReceiptBindingClaimV1 now carries two optional compatibility
fields at the end of its exact record:

    authority_normal_form_version: text | None
    authority_normal_form_root: digest | None

They are an all-or-nothing pair. When present, the version must equal:

    zenodex/fcis/authority-normal-form/v1

The root is recomputed from the exact FCISAuthorityNormalFormV1 value. The
canonical authority projector includes both fields, so the final receipt root
changes when either ANF identity changes.

## Source-bound relation

The D03 entry point requires an exact ANF and checks these fields against the
same evaluation lineage before constructing the accepted receipt:

    ANF.command_root            == evaluation.command_root
    ANF.execution_context_root == evaluation.execution_context_hash
    ANF.pre_state_root          == evaluation.pre_state_root
    ANF.next_state_root         == evaluation.post_state_root
    ANF.support_root            == evaluation.support_root
    ANF.support_set_commitment  == evaluation.support_set_commitment
    ANF.snapshot_commitment     == evaluation.snapshot_commitment
    ANF.patch_root              == recomputed patch root
    ANF.commit_plan_root        == recomputed plan root
    ANF.budget_root             == recomputed budget root
    ANF fee roots               == the exact D02 source segment roots

Missing ANF, wrong exact type, and a foreign command/context/source root return
a typed rejection before an accepted decision is produced.

## Acyclic receipt commitment

The D01 ANF carrier includes a receipt-root field. Hashing the final receipt
and the ANF root into each other would require an unavailable hash fixed point.
D03 therefore fixes the order explicitly:

    base receipt binding
      -> base receipt root
      -> ANF.acceptance_receipt_root == base receipt root
      -> ANF root
      -> final receipt binding including ANF version/root
      -> final receipt root

This gives one deterministic identity without claiming that the D01
acceptance_receipt_root field is already the final receipt root. D04 owns the
remaining bundle and final receipt closure.

## Evidence boundary

Focused tests and the deterministic checker prove the exact source-derived
cross-fields, canonical round trip, ANF-root inclusion, and missing/crossed
rejection cases on the declared fixture. The M5 admission regression remains
green.

The TCG, proof-context, DRA, migration, datastore, caller, and production
no-bypass obligations remain unmounted. A receipt carrying an ANF root is a
lineage commitment, not a production authority witness.
