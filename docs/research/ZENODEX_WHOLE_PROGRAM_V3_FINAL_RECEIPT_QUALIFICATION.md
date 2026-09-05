# Final isolated receipt-chain qualification

Date: 2026-09-05. Authority: `NONE`. Scope: isolated cryptographic verification
and the retained one-command, zero-custody ASSET transfer chain.

The remote batch completed and its evidence was downloaded and hash-checked.
Five genuine Succinct receipts cover ASSET module, coordinator, route,
initialization ROOT and epoch ROOT. The measured Python verifier-set factory
accepted all five with their exact journals and selected images. This supersedes
the pending real-route checkpoint in the earlier publication integration review.
It does not qualify authenticated durable publication or all lane semantics.

## Exact release and artifacts

The final isolated profile is
`0xe7faba74392ffa74dc799037c0c4b7844abbda7224a28d562381be2ea051f993`.
Its verifier registry is
`0x1a53fc8df785c2c4462ca4119c7f6a5affeab717e8c2bf191ba6b00d1649078d`.
The complete measured endpoint-set implementation root is
`0x95eb7de482f19e382ce0ed06a5b43f2b9d96fa0760854ec540380255f67f9f0e`.

| Role | Measured image ID |
| --- | --- |
| Module | `0x5edda34871caacef5194017f61ade9cdfa8c8aeee0e14907824945e58452fc38` |
| Coordinator | `0xa96363692e6397a9eaf92e768a324181077af14e3f3c7b1f7f02741e0eab86c0` |
| Route | `0xfcb2e9e1e032508d3df0899eded32598596bd53621e25d56115700fe0cc12d93` |
| Initialization and epoch ROOT | `0x587c1a7c9c65a98c2d1a76552324f9dcdf2486d88972a6a79d0889ffb5af173b` |

RISC0 SDK 3.0.6, host Rust 1.90 and the retained guest Rust 1.97 compiler were
used. Actual compiler binary SHA-256:
`288ee1994dd8ec08184686e7a52b779c9b075498ffe73003884fefe60389c351`.
Guest source paths affect these images. All final guests were built at one
fixed common source path. Two retained remapping experiments did not establish
portable image reproducibility; neither compiler aliases nor source-byte parity
alone establish that property.

## Retained evidence and independent replay

The local evidence store retains these archives with exact checksums:

| Archive | SHA-256 |
| --- | --- |
| `zenodex-v3-final-root-route-qualification01.tar.gz` | `5ee603a6bce109e32ae52a99b97b2dac5b97fdd10e37321ac1ff7d1e511ab429` |
| `zenodex-v3-final-replay02-subject.tar.gz` | `7a7aff73da3834ba590c3a996ea82fd7d328d901052d7e3fb8cc03e36487d2a1` |

The first archive contains 458 payload files plus its integrity manifest,
including 404 frozen source files, receipts, journals, endpoints and command
logs. Source04 manifest SHA-256:
`134bb02ef7ed2b655acae2bce5b90aae8a24cb0efd2fdf13882236ef3b50dc2a`.
The separately retained Rust reference probe is an appended CPU-only test;
it was not a change to guest code after proving. Its source SHA-256 is
`60eb2b026ef2edfa81cdd82484e7e8636e93a7ac9569900ae54ed33e3c1048eb`.

The unchanged independent Python reference checked the exported Rust state
projection and refinement roots, exact transfer arithmetic and a conserved
misattribution refusal. The CPU reference test passed with
`RISC0_SKIP_BUILD=1` and `--locked --release`; this reference test grants no
receipt authority.

After fixture-builder and local-replay cleanup, all nine rebuilt fixture files
were byte-identical. A fresh measured replay accepted the five real receipts.
Its pre/post audit retained 181 loaded repository files and 24 fixture,
receipt, journal and endpoint files; all 205 were unchanged during execution.
Final replay result SHA-256:
`3bf8171c73579a156aa7d8f9b62a22235e0cb5b0e73a38b1e050725607d548d9`.
Execution required the scoped permission for sealed `/proc/self/fd` binaries;
the earlier sandbox refusal remained `PROCESS_UNAVAILABLE`, with no fallback.

Before integration, all 52 new or changed RISC0 files were compared byte for
byte to retained qualified sources or the explicit reference probe. Comparison
report SHA-256:
`a3486ebc6e9ba11315a7af6d4c94b50805d568185bb73121d63e5d3964f5d853`.
The final integration command will retain the report alongside evidence.

## Claim limits and remaining work

The ROOT composition checks exact child claims, ordering and context. It does
not derive every epoch effect, terminal, body, availability, finality or source
commitment from children. Full runtime checks and mounted publication remain
necessary. See [common-chain review](ZENODEX_WHOLE_PROGRAM_V3_COMMON_CHAIN_REVIEW.md).

The older ROOT 64-command and 65-command refusal tests remain tied to their
earlier image and structural child fixtures. The final common-path image has
the single-command evidence above; no new 64-command qualification is inferred.
The complete command-authentication policy, nonzero-custody composition,
multi-command allocation relation, allocation consumer, initialization ownership
and production shell still require their corresponding evidence.

No proof builds were rerun locally during integration. This checkpoint preserves
the completed remote subject and its replay evidence while publication work
continues. It grants no live profile activation or production writer authority.
