# Command-verifier measurement gap

Date: 2026-09-05. Status: confirmed by static review at
`d1de22436916863e76672459d0d9a4c073c69343`. This note concerns the concrete
BLS command-signature adapter only. No test, build, subprocess, receipt check,
or deployment action was run for this review.

## Static subject pins

| Subject | SHA-256 | Lines | Observed fact |
| --- | --- | --- | --- |
| `src/core/economic_command_signature_verifier_deployment_v1.py` | `b211532aa50ea90747b181cad97cdbdcce5ca65e94907b669f2283031cbe98b6` | 194-202, 205-249 | `implementation_root` hashes one `artifact_bytes` value; binding retains an injected backend. |
| `src/integration/economic_command_signature_verifier_deployment_v1.py` | `a9f93aa7788c55260907c20ac155b62ae385c37d3e60dd000b00a11ad517b55c` | 1-7, 28-49 | The shell reads the caller-selected `artifact_path` and forwards only those bytes to the core. |
| `src/integration/economic_command_bls_signature_verifier_v1.py` | `3dbf54e13400fe84f78bb1be78238c037b43e8e068b4d07bbda68290652a75f9` | 8-12, 20-31, 45-50, 94-96, 127-134 | The fixed backend imports `py_ecc.bls.G2Basic`, calls `Verify`, and delegates artifact measurement to the generic loader. |
| `tools/isolated_bls_evidence_v1.py` | `911d5d71180e6f2ca387f3559848b6306749de9e2f8ce2e70cf9cec364f9bcfe` | 1-5, 22-32, 254-282 | Preparation names the BLS adapter module as `ARTIFACT`, hashes it, and records `loaded_code_correspondence_attested: false`. |
| `tests/integration/test_economic_command_bls_signature_verifier_v1.py` | `8e6f8381fbe50963dfdf16886dc6fb0c8f3298739f5e74e5aa02c80148e4c88d` | 60-70, 297-304 | The fixture measures `Path(bls_verifier.__file__)`; its negative control changes that selected adapter artifact. |
| `src/integration/global_receipt_verifier_v1.py` | `5e727d826ea298559e3bc2136fe96dec62f2d56eb66e6488771e652b699fcd47` | 1-7, 100-120, 136-172, 202-214 | A separate receipt endpoint adapter measures an ELF, seals a memfd snapshot, and executes its receipt protocol. |

Here, “wrapper” means
`src/integration/economic_command_bls_signature_verifier_v1.py`, the actual
adapter selected by both preparation and the concrete-binder test.

## Confirmed gap

The implementation root is a hash of the supplied artifact bytes alone. The
fixed BLS path subsequently executes the imported `py_ecc` object. Therefore,
the root can identify the selected adapter module while omitting some code that
performs cryptographic verification. This is an inference from the pinned call
and measurement paths; it is not an exploit claim.

The artifact-loader and BLS tests exercise stable regular-file acquisition and
rejection for a changed selected artifact. They do not establish that the
`py_ecc` module and its executed dependency closure equal a release-bound
execution subject. Preparation records a broader source/runtime snapshot, then
explicitly leaves loaded-code correspondence unattested. That preserves the
existing claim ceiling; it does not turn the adapter-file root into an execution
root.

## Separate receipt subject

The receipt bridge's ELF hash, sealed memfd, and `/proc/self/fd` launch bind a
receipt-verifier executable for receipt/image/journal requests. The BLS adapter
does not import or invoke that bridge. Its existing seal must not be described
as BLS implementation measurement. It is a suitable implementation pattern
for a future BLS-specific subprocess, while its receipt semantics and authority
remain separate.

## Existing honest nonclaims

`ZENODEX_WHOLE_PROGRAM_V3_BLS_INPUT_PREPARATION_REPLAY.md`
(`16de4267bea8db5075d5ceb43dd9fe0186ec09fe84cd54573d02cddae5dfd632`)
states that the installed dependency snapshot is observed rather than proof of
loaded-code correspondence (lines 60-75), and retains loaded Python/dependency
correspondence as a separate obligation (lines 171-176).

`ZENODEX_WHOLE_PROGRAM_V3_BLS_PROOF_PREPARATION.md`
(`2b2a93e2ceadf3d1606454d3d2837f322185fba0aa82e82a3a5b16258c30c497`)
calls environment capture provenance rather than proof of arbitrary measured
bytes being loaded (lines 79-88), and keeps loaded-code correspondence a
trusted-process premise (lines 181-187). These statements remain accurate.

## Smallest bounded closure packet

1. Define a BLS-only request/response protocol for exact algorithm, public key,
   message, signature, and a closed accept/reject result. It must not reuse the
   receipt protocol or receipt authority.
2. Deliver one fixed BLS verifier executable whose cryptographic implementation
   is inside the measured executable, or whose complete executable closure is
   measured and verified before launch. A measured Python adapter alone is not
   sufficient.
3. Add a BLS-specific sealed-execution adapter using the receipt bridge's
   copy/hash/seal/descriptor pattern. Bind the measured BLS execution root and
   protocol root in the BLS release/manifest before accepting any verification.
4. Route a new, explicitly selected BLS deployment through that adapter.
   Preserve historical profile decoding; existing releases must not silently
   acquire a different execution meaning.
5. Require focused evidence for changed executable bytes, replacement after
   measurement, malformed or mismatched responses, and a genuine BLS positive
   plus wrong-key/message/signature rejections. The execution-root assertion
   must fail if the selected BLS executable differs from the release subject.
   Timeout, malformed output, and unavailable verification must fail closed;
   authentication rejection must produce no receipt-verifier call or economic
   effect in the restricted publisher pipeline.

This packet could establish only that the local BLS call ran the pinned BLS
execution subject under its stated process premise. Kernel, dynamic-loader and
OS trust, receipt validity, authentication authorization, publication, and any
production conclusion remain outside that result.
