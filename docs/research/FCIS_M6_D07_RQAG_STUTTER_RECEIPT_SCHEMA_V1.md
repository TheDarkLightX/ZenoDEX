# FCIS M6 D07 RQAG Stutter Receipt Schema V1

TASK_ID: D07

## Purpose

D07 supplies the residual-fiber certificate used when a runtime trace removes
an operation as an observational stutter. The receipt is a controlled value
created only by verify_stutter_candidate_v1.

The receipt is evidence for quotienting a trace. It has no authority to create a
commit, publish an acknowledgment, advance migration, or move value.

## Receipt fields

StutterReceiptV1 contains:

- operation_id: one canonical 0x-prefixed operation identity root;
- operation_kind: one closed eligible operation enum value;
- pre_canonical_root: exact canonical state before the operation;
- post_canonical_root: exact canonical state after the operation;
- observable_root: the common observable state/effect root;
- checker_id: the pinned checker enum value for operation_kind;
- verification_root: a derived root binding all preceding fields.

The receipt exposes receipt_root as a derived value. It is not caller-selected.

Operation kind is explicit because operation identity and operation class have
different roles. The operation identity binds the concrete repeated operation;
the closed kind determines which checker is permitted.

## Eligible operations

The only receipt-producing kinds are:

- same_commit_retry;
- canonical_reopen_reencode;
- same_effect_destination_dedup;
- repeat_pure_verification.

Each kind has exactly one pinned checker ID. The checker ID is derived from the
closed kind and cannot be supplied independently.

## Acceptance relation

A candidate is accepted as a stutter only when:

pre_canonical_root == post_canonical_root
observable_pre_root == observable_post_root
operation_kind is an eligible closed enum member
all roots are exact lowercase 0x-prefixed 32-byte roots
the derived verification root recomputes exactly

The receipt stores the common observable root after the equality check.

## Forbidden operations

The model explicitly enumerates and rejects:

- new_commit;
- ack_publication;
- migration.

A string or other untyped value with one of those names also rejects at the
operation-kind boundary. A caller cannot construct a receipt with a foreign
checker ID or verification root because construction requires a private token
and revalidation recomputes both bindings.

## Root construction

The verification root is:

H(
  zenodex/fcis/rqag/stutter-verification/v1,
  operation_id,
  operation_kind,
  pre_canonical_root,
  post_canonical_root,
  observable_root,
  checker_id
)

The receipt root is:

H(
  zenodex/fcis/rqag/stutter-receipt/v1,
  operation_id,
  operation_kind,
  pre_canonical_root,
  post_canonical_root,
  observable_root,
  checker_id,
  verification_root
)

All fields use canonical length framing and the repository domain-separation
helper.

## Boundary

D07 is tested unmounted evidence for a finite RQAG receipt language. It does
not prove that an external caller truthfully classified a concrete database
operation, that a destination actually deduplicates effects, that canonical
reopen covers production storage, or that TCG quotient completeness is mounted.
