# GlobalSettlementABI V1 Rust Reference

Status: `RESEARCH_ONLY_UNMOUNTED`

This standalone crate owns typed decode, structural validation, canonical JSON,
and domain-separated root recomputation for the GlobalSettlementABI V1
reference. It exposes receipt-verifier ports and opaque verified module, lane,
route, and bounded epoch witnesses for contract testing. This crate exposes no
RISC0 verifier implementation, authenticated verifier registry, database
adapter, ledger writer, or publication witness. The isolated sibling crate
`zk/global_economic_epoch_risc0` exercises the direct recursive statement while
remaining unmounted.

The crate uses unsigned 64-bit control fields, unsigned 128-bit non-negative
atom quantities, and signed 128-bit effect deltas. Unknown JSON fields reject.
Validation is explicit after owned decode. The shared Python-generated fixture
contains seventeen vectors and includes `2^64 + 1` atoms.

The asset-precision kernel adds a closed, canonically ordered policy registry
for scales from zero through eighteen decimals. Successor G1 profiles select
eight-decimal ledger atoms, a four-decimal `bv[24]` Tau-testnet adapter, and an
eight-decimal `bv[64]` Tau target. Upscaling uses checked powers of ten;
downscaling requires exact divisibility. Percentage-burn quotes use quotient and
remainder decomposition to avoid a wide intermediate, expose the fractional
residue over 10,000, and require explicit asset retirement before the final atom
can be burned. The registry and arithmetic functions remain unmounted and have
no profile, Tau-runtime, guest, or writer authority.

The crate also contains the first research-only lane core for authenticated
account transfer. Its typed transition applies a profile-owned flat fee,
emits canonical account, fee, conservation, lane-write, and occurrence effects,
and makes every typed rejection an exact no-op. Python and Rust tests lock one
transfer vector to the same six canonical byte hashes and five derived roots.
Zero-fee split/merge and fee-owner alias cases exercise deterministic state
composition.

A separately versioned managed-asset lifecycle core adds profile-bound generic
issue and self-burn for registered ordinary tokens. It rejects generic supply
authority for native coin, canonical zUSD, LP shares, ZDEX, and sealed-bid
assets. Python and Rust lock both variants to identical canonical bytes and
roots. Neither core is selected by a mounted route or writer. External
custody, protocol-specific supply transitions, guests, receipt verification,
writer adapters, and publication authority remain absent.

The asset-lane coordinator adds one common accounts, named-custody, and supply
projection. Its private port binds producer schema, module release, occurrence,
complete pre/post projections, effects, and terminal obligations. It checks all
journal and policy bindings, exact movement deltas, absolute conservation rows,
and reject-is-no-op before normalizing the lane write to common projection
roots. Python and Rust lock the same coordinator vector to seven canonical-byte
hashes and six roots.

Existing module V1 journals carry a zero private-port root and fail coordinator
admission. Bound acceptance tests use synthetic structural journals. The crate
now also exposes a guest-ready asset-transfer lane wrapper that constructs the
accepted private port, deterministic receipt root, and rebound journal inside
the module output. Python and Rust tests lock six shared roots, direct
coordinator admission without fixture rebinding, policy-root sensitivity, and
reject-is-no-op behavior.

The managed-asset lifecycle now has the same guest-ready boundary for both
profile-authorized ordinary-token issue and owner-authorized self-burn. Its
accepted result owns the common private port and rebound journal; Python and
Rust lock twelve issue/burn roots plus direct coordinator admission. The named
protocol-asset exclusions remain enforced by the underlying lifecycle core.

The release-route binder now takes the complete typed module input and accepted
output, derives the active command route, checks the profile lane release and
all occurrence and domain bindings, and returns a constructor-controlled
structural witness. Python and Rust pin the same binding root and reject
caller-selected routes, inactive profiles, wrong releases, cross-domain
substitution, and issue-occurrence to burn-output relabeling. The witness does
not verify a cryptographic receipt and is not accepted by a mounted writer.

The module-receipt verifier boundary recomputes that structural witness from
the complete typed input and accepted output, selects the active lane release's
guest image, requires explicit `SUCCINCT` receipt kind and nonempty bytes, and
passes the exact canonical module journal bytes to an injected cryptographic
verifier port. Only verifier acceptance constructs
`VerifiedLaneModuleTransitionV1`. Python and Rust pin the verified binding,
journal-byte digest, and receipt digest to identical roots. The verifier
implementation, verifier-registry authentication, real guest receipts, epoch
recursion, and ledger publication remain absent.

The receipt-backed asset-lane composition boundary now pairs that opaque
verified-module witness with the exact module journal, active single-lane route,
coordinator context, private port, and deterministic coordinator result. It
rejects valid-receipt substitution across module journals and returns an opaque
`RECEIPT_BACKED_STRUCTURAL_ONLY` candidate. A governed coordinator registry now
selects the exact coordinator image and source/toolchain roots. Receipt
verification of the exact canonical lane journal is the only constructor for
`VerifiedLaneCompositionV1`.

Route releases now commit the route-composer image, specification, source, and
toolchain roots in their content-derived release IDs. The route receipt boundary
requires the exact ordered lane journals and opaque verified-lane witnesses,
then verifies the canonical route journal under that governed image before
constructing `VerifiedRouteCompositionV1`. It also exposes the public
route-assumption root that binds the exact profile, route release, occurrence,
writer epoch, route-journal root and digest, and expected child image. This
route witness is an input to bounded epoch admission and exposes no standalone
epoch, commit, settlement, or publication authority.

The epoch receipt boundary consumes one immutable
`EconomicEpochReceiptCandidateV1` in both language references and requires one
exact opaque route witness for every canonical occurrence and route journal.
It checks governed route release and image, writer epoch, lane order,
route-journal root and canonical digest, exact public route-assumption root,
and one disclosed effect plan whose root and occurrence match that route
journal. A pure checked composer folds the route plans into the only admissible
certificate-bound epoch plan. The current closed composition law accepts only
sequential single-lane `ASSET_TRANSFER` routes with zero terminal obligations
and no external outbox rows. It checks signed and unsigned arithmetic,
connected lane and conservation histories, unique occurrence consumption,
sequential pre/post roots, canonical order, root receipt kind and digest, and
the active profile's root image before constructing `VerifiedEconomicEpochV1`.
Python and Rust share a golden aggregate effect-plan root and the commit
identifier over the certificate root, ordered route-witness binding roots, and
root receipt digest. Boundary tests cover 1, 8, 9, and 64 routes plus unrelated
epoch plans, wrong route roots, disconnected histories, duplicate occurrences,
overflow, zero, 65, missing, foreign, reordered, empty, wrong-kind, and
verifier-rejected evidence.

The deterministic receipt roots are statement commitments, not cryptographic
proof receipts. This ABI crate contains no guest or cryptographic verifier
implementation, so its legacy fixtures and module-owned outputs establish
deterministic contract behavior only. The sibling pinned RISC0 3.0.6 crate has
one real direct-recursion test, yet that test consumes a quarantined structural
child which proves no economics. Guest-backed release registration,
authenticated verifier selection, economic route receipts, guest-proved effect
aggregation, multi-lane and terminal composition, the full 64-command replay,
and cross-release coexistence evidence remain open. The deterministic host-side
composer grants no proof, settlement, commit, or publication authority by
itself.

## Dependency decision

All direct versions and transitive checksums are exact in `Cargo.lock`.

- `serde 1.0.228` and `serde_json 1.0.148` provide owned typed decode and the
  sorted JSON value used by the existing Python ABI. `arbitrary_precision` is
  required so u128 values remain exact. Both use the MIT or Apache-2.0 license.
- `sha2 0.10.9` implements the specified SHA-256 roots without host services or
  nondeterministic inputs. It uses the MIT or Apache-2.0 license and disables
  default features.
- `hex 0.4.3` encodes fixed SHA-256 outputs as lowercase hexadecimal. It uses
  the MIT or Apache-2.0 license and adds no transitive packages.

The lock contains 22 packages. These versions are already present in the local
RISC0 research dependency closure, so the offline test does not fetch code.
The removal alternative is a separately reviewed canonical codec, SHA-256
implementation, and fixed-hex encoder. That alternative would enlarge the
local cryptographic and serialization surface. No dependency or advisory claim
is promoted until the release SBOM and current advisory gates cover this crate.

## Replay

```bash
PYTHONPATH=. python3 tools/render_global_settlement_abi_v1_golden.py \
  --check tests/data/global_settlement_abi_v1_golden.json

cargo test --offline --locked \
  --manifest-path zk/global_settlement_abi_v1/Cargo.toml

cargo clippy --offline --locked \
  --manifest-path zk/global_settlement_abi_v1/Cargo.toml \
  --all-targets -- -D warnings

cd zk/global_economic_epoch_risc0
cargo test --locked -p zenodex-global-economic-epoch-risc0-shared
RISC0_SKIP_BUILD=1 cargo test --locked --workspace
cargo clippy --locked --workspace --all-targets -- -D warnings
```

These commands establish local typed parity, transfer and ordinary-token
lifecycle semantics, single-module lane composition, governed route and
coordinator image selection, exact-journal verifier-port behavior, and
negative-test evidence only.
The sibling replay adds direct guest compilation and tested one-through-eight
assumption preflight. Cycle benchmarks, economic child proofs, full 64-command
aggregation, guest-proved route-effect composition, source-finality, release
authority, durable atomic publication, and production readiness remain open.
