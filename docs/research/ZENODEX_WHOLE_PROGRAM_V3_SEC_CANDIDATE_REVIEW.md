# V3 SEC interface candidate: engineering integration review

2026-09-05. Candidate `b802c942a8c7ccf8bf17b1b61021cbd8c960b7ea`,
sole parent `32e27d438a6149d5d2c0d971f61ee7f260000d76`, tree
`63ef49159741a1ff4ef250ad7ad35966f185ad14`. Current comparison baseline:
`d02e2693476e597bbbb7cae75fb2905e004b0fff`, with the exact relevant bytes
listed below. Concurrent economic integration changes were preserved.

Disposition: **SELECTIVE_INTEGRATION_REQUIRES_REPAIR**. The candidate changes
seven files and has no economic-kernel, receipt-verifier or publisher edits.
Its exact patch fails `git apply --check` against the current API-server and
request-grammar-test contexts. Nothing was applied, cherry-picked, reset or
renamed. This review concerns software behavior and evidence compatibility;
it neither verifies nor endorses the candidate's legal interpretations.

## Findings

| ID | Observation | Required integration treatment |
| --- | --- | --- |
| SEC-R01 | The new body preflight catches JSON syntax/Unicode decoding errors but propagates parser `RecursionError` and other `ValueError` outcomes. Its iterative traversal does not protect the preceding JSON parse. | Reuse the current typed parser-failure handling; define refusal before dispatch without an unhandled parser error. Controlled faults on an ordinary empty object confirmed the difference without resource-exhausting input. |
| SEC-R02 | Current `http_authority_ingress_v1.py` already preserves duplicate object entries, refuses unscannable depth/node/stack growth and covers raw-authority field families. The candidate uses ordinary lossy `json.loads` and a narrower exact vocabulary. Duplicate parent members can erase earlier nested entries before its scan. | Preserve the existing parser/classifier guarantees. Do not replace it with the candidate predicate or parse a lossy object first. Candidate normalization/vocabulary may inform a reviewed extension. |
| SEC-R03 | The candidate scans POST bodies before handler authentication. Current DEX/sealed-bid guards run after `_demo_auth_ok`, and retained tests require authentication precedence. The candidate vocabulary also refuses `seed`, while the current classifier explicitly accepts a numeric seed as a public field. | State and test ordering/error-code compatibility and field-policy scope explicitly. The 42 historical grammar outcomes do not establish current compatibility or prove that no currently supported input changes. |
| SEC-R04 | The candidate's 300,000-node justification assumes a 262,144-byte maximum body. Current `_max_post_body_bytes_for_path` includes an 8,388,608-byte autogov branch; the candidate test's hand-picked probes omit it. | Reuse explicit bounded rejection rather than claiming the budget is unreachable. Enumerate every actual ingress/body limit when checking this relationship. A byte ceiling does not promise that every document below it satisfies a node/depth ceiling. |
| SEC-R05 | The terminology test demands that the string `custody_domain` disappear from `src/`. The current baseline has 31 tracked source files containing it, including canonical state/effect contracts. | Preserve existing V1/V2 fields and roots. A terminology recommendation cannot authorize a canonical wire rename, reinterpretation or evidence regeneration. Correct the stale document/test premise rather than forcing a schema migration. |
| SEC-R06 | Candidate code/docs state that refusing named fields prevents all server access to key material. Body bytes are already acquired and decoded before this check; the predicate inspects field names, not arbitrary values or all infrastructure. | Describe the mechanical guarantee as refusal of recognized fields before the selected handler boundary. Request-line logging is redacted in both subjects; upstream proxies, alternate ingress and all key-control/authorization behavior are separate investigations. |

SEC-R02 is a static parser-information finding; no request demonstrating a
guard bypass was sent or generated. The candidate predicate is useful as a
small field-name filter within its honest scope. It is not a complete key-flow,
authentication, authorization or publication control.

## Current reachability and compatibility

The current `_Handler.do_GET` and `do_POST` normalize a path before dispatch.
`_reject_authenticated_raw_authority_material` is mounted in
`_maybe_handle_dex_api` and `_maybe_handle_confidential_sealed_bid_api` after
authentication. Its existing codes are `raw_authority_material_forbidden` and
`authority_material_scan_refused`. The candidate adds different refusal codes
at a different boundary. Retained perps-wallet, zUSD and autotrader research
handlers must not be re-enabled as a side effect of importing its older API
server. A query-name refusal can be reviewed separately without altering those
writer quarantines or copying the older dispatch tree.

The current JavaScript `walletSignerPolicy.js` is byte-identical to the
candidate's version. Its `hasSecretField` recursively inspects signer-related
objects and responses; the candidate Python filter scans incoming JSON/query
objects iteratively. The candidate's tests compare the vocabulary extracted
from source and one normalization example. That is narrower than complete
cross-language parser, recursion/resource or request-schema parity. The
additional bounded replay below confirms 33 ordinary shared classifications,
including nested objects/arrays and normalized names; it makes no universal
Unicode or arbitrary-object claim.

The candidate body hook also depends on the existing explicit list of POST
prefixes. Adding a future route outside that list would require a new mount
decision; placing a function in `do_POST` does not establish universal future
mediation. HTTP headers, direct Python calls and other servers remain outside
this field filter. The fixed measured economic admission pipeline is a
separate interface and receives no authority from this candidate.

## Executed observations and retained packet

The review used the exact commit-to-parent diff, relevant current callers and
read-only application checking. It executed no HTTP server, external request,
large parser input, stress campaign or new build.

The retained review packet contains `replay.py`, exact candidate source copies,
`report.json`, `current-ui-scan.json` and `scanner-status.json`. Replay command,
from the reviewed repository root:

```sh
PYTHONPATH=. PYTHONDONTWRITEBYTECODE=1 python3 <retained-review-packet>/replay.py
```

The script loads the exact candidate guard and extracts the unchanged body
method AST and JavaScript predicate. It runs 33 small Python/Node predicate
comparisons, ordinary empty/malformed-body/query controls and an explicit
zero-budget refusal. For each of two controlled parser exceptions it replaces
`json.loads` on the benign input `{}`: the candidate propagates the exception,
while the current guard returns `SCAN_REFUSED`. It separately evaluates current
body-limit code without serving traffic. All review assertions passed.
Node reported `v20.19.2`.

`python3 tools/covered_ui_lint.py --strict` returned exit status 1, scanning
109 files with five lexical findings, rather than the candidate document's
109/0 result. They concern text in `PoolDashboard.jsx`,
`ZUSDMonetarySurface.jsx` and `perps/PerpLiveWalletSurface.jsx`. These are
scanner signals, not findings about actual custody, settlement authority or
legal status. Review the behavior and intended wording before any amendment;
do not mechanically rename accounting fields or suppress truthful UI text to
satisfy a lexical rule. No scanner snapshot or expected count was changed.

The candidate's reported 186 Python tests, 22 Node tests and mutation-ledger
counts were not independently replayed on its full historical tree. Current
mounted HTTP tests and the full request-grammar campaign were not rerun here.
Those remain required after any actual current-source integration. Regenerate
path fingerprints by the retained minimizer command against that exact source;
the candidate's historical fingerprint is not transferable evidence.

## Exact subjects

| Subject | SHA-256 |
| --- | --- |
| Candidate `src/integration/secret_material_guard.py` | `3552aac729bd9c5e0886484cc56684476358bdeea189a863a587a09739dcb8ac` |
| Candidate `src/integration/api_server.py` | `d19411d836fc01851b3e85b764220919bc2d4fc8bbf9cf09a007164a00afb837` |
| Candidate/current `tools/dex-ui/src/sdk/walletSignerPolicy.js` | `2a03a133e8ca425d970802e8a7085e476bc8b97e51a667c9cf47e7c57349e96d` |
| Candidate `tests/integration/test_secret_material_guard.py` | `6e2bdfe7dce64afaf952c0e580ecd5cd5bea612f608241635bbde0fd91057bb0` |
| Candidate `tests/integration/test_sec_crypto_interface_controls.py` | `6d503dec130e8c21ed422e03c192d28cc535df01688203f6c63ec7801136c9be` |
| Candidate `tests/integration/test_api_server_request_grammar_fuzz.py` | `f824158de591fa1b1e1468150d2638d0d600e8aed503e5ff31478c6c9348aca9` |
| Current `src/integration/api_server.py` | `8043ee569a6292b8b1bb35fffb287c09160c2179b2372a4ff3ab91e42070d4d2` |
| Current `src/integration/http_authority_ingress_v1.py` | `409833388bbcdf34b4256885470e1b5354d9a7ddc6a74ca15ea59e8de12743b0` |
| Current `tests/integration/test_http_authority_ingress_v1.py` | `1b2fbc0d8b35ac435e3b6e67524c26177ee55314aed49a8b5a71022caaa13680` |
| Current `tools/covered_ui_lint.py` | `7e68dadcc9582ec79c07ae4ae075d37e83b240885b0a413f3b194083835b4136` |
| Review packet `replay.py` | `0c47c8f26230304aec630c1b4320a103d4bdb6b26d1a13daeb7f0b2a0cbae9a6` |
| Review packet `report.json` | `97715209caf24a7470db13ba172c22be171274683df35acf3547e3b95f8c87f7` |

The safe next integration packet should extend the existing ingress contract,
retain its typed and duplicate-preserving parser, explicitly choose query and
field-policy scope, preserve authentication precedence and wire identities,
and replay current caller/grammar evidence. Legal-source/status verification
is a separate task; none of those claims is admitted by this review.
