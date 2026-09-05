# Isolated BLS-authenticated proof subject preparation

Prepared 2026-09-05 against integration commit
`38c4a75e0e9dc9f7cc16c2297407fc54d53d90d8`. This records the prerequisite
analysis before the signature-purpose repair. It creates no release, chooses
no product policy and launches no prover. The existing single-transfer test
allocation remains the proposed isolated input; its genesis ownership is an
explicit assumption.

## Blocking selector and bounded repair

The existing signature registry selects only one `ACTIVE_NEW` release with
`accepts_new_authentications=true`. Construction of that status requires all
ten evidence labels, including `NO_BYPASS` and `RELEASE_BACKED`. A real BLS
signature and a real RISC0 receipt cannot establish those deployment claims.
The current real-BLS unit fixtures explicitly synthesize those labels; they
are unsuitable as evidence-backed release manifests for the next proof batch.

The authorized repair is explicit `PRODUCTION_NEW` and
`ISOLATED_QUALIFICATION` purposes. Production defaults, existing canonical
wire/profile bytes, and historical production binding roots remain stable.
Isolation selects a `SHADOW` signature release whose production-acceptance
flag remains false. Its minimum evidence is `SPECIFIED`, `IMPLEMENTED`,
`TESTED`, `SOURCE_PINNED`, and `TOOLCHAIN_PINNED`, matching the existing
receipt-verifier precedent. Existing historical SHADOW records need not be
rewritten; the new selector checks the floor when admitting isolation.

Purpose must be carried in the separately owned verifier authority and the
authenticated intent/occurrence witnesses. Isolated identities use a distinct
domain and explicit purpose. The ordinary production authentication entry
rejects an isolated verifier. Binding an intent to an occurrence must preserve
the purpose; the module's existing authenticated-command binding commits it.
The private-minted isolated pipeline fixes isolation internally. An enum in a
manifest alone would not close this boundary.

The affected Python contract comprises the signature registry, deployment
binder, opaque capability, authentication helper/witness, artifact loader, BLS
convenience binder and isolated pipeline. Tests must retain existing production
byte goldens and reject wrong purposes, unknown enum values, revoked releases,
missing evidence, foreign deployment/profile/policy, stale disclosures and
purpose stripping. No guest signature-verification statement is introduced.

## Retained subject and image reuse

The previous profile is
`0xe7faba74392ffa74dc799037c0c4b7844abbda7224a28d562381be2ea051f993`.
Its signature-registry root
`0x6177b564c5c54f398cb3ea06cf637d043fd501adb328887eb6e73e6c7a4af5ba`
was independently reconstructed from the retained Rust fixture. It commits
the artifact string `asset-lane-host-command-signature-verifier-test-artifact-v1`
and test release
`0x19558fb08ea813aaf3ec7555f167bd8a1e9443495db50d4ef0c14aad0d4236b4`.
Its source uses the placeholder public key `bls12-381-g2:alice-public-key`.
Rebuilding that authorization against the final route yields a different root
from the retained authorization root. The final fixture therefore supplies no
signer-authorization qualification, as its retained subject explicitly states.

These four retained executables were rehashed during preparation:

| Role | Compiled image ID | Verifier executable SHA-256 |
| --- | --- | --- |
| Module | `0x5edda34871caacef5194017f61ade9cdfa8c8aeee0e14907824945e58452fc38` | `04785a1f721a077ba2012a41c6b9b102e997bcb639c596c4230cf114ec5e0297` |
| Coordinator | `0xa96363692e6397a9eaf92e768a324181077af14e3f3c7b1f7f02741e0eab86c0` | `34d0c733f2a21a015ecb5ac992e22a7bed29786cac9a2f8e221d1ed33fb9b08d` |
| Route | `0xfcb2e9e1e032508d3df0899eded32598596bd53621e25d56115700fe0cc12d93` | `f982ad0bd804db85c80592537bcb0881238f3b0bb22be366b401aaa05261f615` |
| Root | `0x587c1a7c9c65a98c2d1a76552324f9dcdf2486d88972a6a79d0889ffb5af173b` | `6bfd498ad314d82cd2381efa76d97c376d8e643918d41e74e350986d672c6adb` |

Source inspection indicates that changed profile and policy inputs can be
supplied to these unchanged guests: authentication remains a separately checked
host condition, while the guests bind the selected profile and exact transition
context. This is a compatibility proposal until the new complete inputs pass
the retained host preflights and genuine proofs. A new image is unnecessary
solely because an input profile changed. If any actual guest, dependency, build
path or compiler input changes, remeasure the affected chain before reuse.
The previous builds remain bound to their recorded common physical build path;
portable reproducibility is still unqualified.

## Concrete input construction order

1. Freeze the purpose repair, BLS backend, core message constructor, loader and
   raw-evidence pipeline. Capture their exact source hashes and test reports.
   Acquire a bounded regular BLS artifact through the existing loader. Hash
   its actual bytes; retain the artifact preimage separately from its digest.
2. Capture the actual interpreter and installed dependency closure used by the
   BLS call. Record package versions, each installed source/native artifact
   hash, distribution metadata and canonical closure-manifest hash. This is
   observed environment provenance, not proof that arbitrary measured bytes
   are the loaded implementation. Do not include credentials, caches, user
   configuration or unrelated installed packages.
3. Build the SHADOW signature manifest/release from actual retained evidence.
   Evidence dependencies must end at earlier immutable artifacts. In
   particular, an implementation-test report used by this manifest must not
   include the not-yet-created final profile or signature being constructed.
4. Select a public deterministic test key and disclose its canonical lowercase
   `0x`-prefixed 48-byte G1 public key. The scalar is test data, never a deployed
   secret. Create the authorization row against the **final** selected route,
   exact subject/grant and explicit test height/nonce bounds. Recompute both
   signature and authorization registry roots; preserve every other selected
   policy binding unless its exact input changed.
5. Derive the genesis source manifest from explicit allocation-row occurrences
   and a prior, profile-independent isolated allocation assumption. Include
   each source-authorization preimage. The existing builder hashes the old
   complete state before rebinding its profile; copying that recipe would
   describe an old state rather than authorize the final one. Hashing the
   final full state into a policy committed by its own profile would create a
   cycle. Bind the test allocation rows independently, then bind the final
   complete state in the initial-state statement. Genesis ownership remains
   unverified.
6. Construct the final policy registry and profile, then the pre-state root,
   command occurrence, module/coordinator contexts, deterministic post-state
   and replay row. Recompute every affected root. Input position remains the
   single supported occurrence until the wider pipeline is independently
   qualified. Nonzero custody retains its known coordinator limitation.
7. Construct the canonical economic intent and envelope using the new isolated
   message entry. Sign the core's exact raw domain-separated message with
   G2Basic, without an additional SHA-256 prehash. Retain the message, signature,
   command body and registry disclosures. Reauthenticate through the concrete
   isolated factory; retain genuine wrong-message/key/purpose controls.
8. Preflight the exact route input through the retained Rust preparation and
   independent Python reference. Produce the module, coordinator and route
   succinct receipts, retaining native JSON receipts and exact journals.
   Prove initialization under the same Root image. Form the epoch input from
   the exact proved route journal, preserving little-endian RISC0 image-word
   conversion, and prove the final Root epoch with that route assumption.
9. Replay all five receipts through the four measured endpoints. Supply the
   raw BLS disclosures and three native child receipts to the new isolated
   pipeline, then run allocation, epoch and isolated publication admission.
   Preserve each independent rejection and logical no-effect observation.
   A receipt proves execution under its recorded assumptions; it does not
   authenticate genesis ownership or grant live publication authority.

The final batch should retain `initial.input.json`, `route.input.json`,
`epoch.input.json`, all three policy/authorization/signature registry
disclosures, the signature release/manifest/artifact, exact signed-message
bytes and signature, all five receipts/journals, all four ELFs/endpoints,
source/build/dependency manifests, commands and complete positive/negative
reports. Finish every local deterministic preflight before requesting a
prover session. No new batch has been launched by this preparation.

## Observed local BLS environment

The initial inspection observed CPython 3.12.3; interpreter binary SHA-256
`1643dacd9feaedc58f3cc581e4d22577dfe25c09b10282936186ccf0f2e61118`.
Installed metadata resolves py-ecc 8.0.0, eth-typing 5.2.1, eth-utils 5.3.1,
eth-hash 0.7.1, cytoolz 1.1.0, toolz 1.1.0, typing_extensions 4.15.0,
pydantic 2.12.5, pydantic_core 2.41.5, annotated-types 0.7.0 and
typing-inspection 0.4.2. This inventory is not the required per-file closure
measurement or a portable dependency lock. The repository requirement
`py-ecc>=6.1.0` alone does not pin that observed subject.

Preparation source SHA-256s, before purpose repair:

| Source | SHA-256 |
| --- | --- |
| `economic_command_bls_signature_verifier_v1.py` | `f19644aa318824c8308622f5cc78b218890517661b94f56d8292e94a38da0c82` |
| `isolated_asset_receipt_pipeline_v1.py` | `27f5dfcc08b9c2644fd129f60418c0f237739d653b81a13a8103009ad0c31a50` |
| `economic_command_authentication_v1.py` | `c66448fb090a687aebfa00b1fa31b01099e24087e8cbf50ce9763b5c03e0d8d0` |
| `economic_command_signature_verifier_registry_v1.py` | `4579eb3dac9ec631e98bf82127948483d4236bf91636e0c6c6e19a753b53275a` |
| `build_isolated_fixture.py` | `42ce529873126dc91d399d248cbe4778e143163934a99a188478d75ec3052ee6` |

Existing economic kernels own amounts, fee allocation and state transitions;
the preparation layer only supplies typed inputs and preserves their results.
There is no state mutation or commit point in the purpose repair. New scoped
capabilities must retain defensive snapshots and fail closed on stale policy
or release status. Existing production golden vectors are the compatibility
oracle; the new purpose has no Rust-runtime parity or formal refinement claim
until those separate obligations are discharged.

## Purpose implementation replay

The subsequent Python repair implements the explicit purposes described above.
`_authenticate_isolated_economic_command_intent_v1` is the isolated pipeline
entry; `authenticate_economic_command_intent_v1` retains the production default.
The artifact loader, BLS binder and capability require the selected purpose.
Binding an intent to an occurrence retains it. Production identities continue
to use their historical hash domains and bytes; isolated identities additionally
commit the purpose under distinct domains. Existing serialized registries,
profiles and guest journals are unchanged.

The isolated evidence floor describes these restricted subjects:

| Status | Required retained evidence | Explicit limit |
| --- | --- | --- |
| `SPECIFIED` | Exact algorithm, raw message, canonical key/signature and purpose contract | Does not certify economic policy |
| `IMPLEMENTED` | Selected backend/loader source and acquired artifact | Loaded-code correspondence remains a trusted-process premise |
| `TESTED` | Source-bound real BLS and rejection controls | Synthetic RISC0 process replies are not cryptographic receipt evidence |
| `SOURCE_PINNED` | Exact artifact and relevant source hashes with preimages | Hashing a file does not prove the interpreter executes that file |
| `TOOLCHAIN_PINNED` | Observed interpreter and dependency-closure measurements | Does not establish OS integrity or portable reproducibility |

No labels are added automatically and no evidence artifact is manufactured by
the selector or factory. The next batch still requires the actual per-file
closure measurement and retained evidence preimages described above. The new
purpose tests use explicitly synthetic evidence roots and real BLS signatures.

Executed with `PYTHONDONTWRITEBYTECODE=1` and pytest `-p no:cacheprovider`:

```text
python3 -m pytest -q -x -p no:cacheprovider
  tests/core/test_economic_command_signature_verifier_purpose_v1.py
  tests/core/test_economic_command_authentication_v1.py
  tests/core/test_economic_command_signature_verifier_deployment_v1.py
  tests/core/test_economic_command_signature_verifier_registry_v1.py
  tests/integration/test_economic_command_signature_verifier_artifact_loader_v1.py
  tests/integration/test_economic_command_bls_signature_verifier_v1.py
173 passed in 16.92s, including 21 new purpose controls

python3 -m pytest -q -x -p no:cacheprovider
  tests/core/test_lane_module_release_route_binding_v1.py
  tests/core/test_perps_margin_release_receipt_binding_v1.py
  tests/core/test_receipt_backed_asset_lane_composition_boundaries_v1.py
  tests/core/test_receipt_backed_perps_margin_lane_composition_v1.py
98 passed in 24.36s
```

Focused mypy passed for all eight changed source files. The new isolated
purpose has no Rust implementation or proof-refinement claim; the retained
legacy production cross-language byte goldens passed unchanged. No new RISC0
guest build, genuine receipt generation, live profile activation or balance
migration occurred during this repair.
