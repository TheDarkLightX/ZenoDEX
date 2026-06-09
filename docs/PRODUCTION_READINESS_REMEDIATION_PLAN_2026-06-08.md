# ZenoDEX Production-Readiness Remediation Plan (2026-06-08)

Source: 4 read-only audits (UI wiring / backend API / end-to-end / production posture).

## Scope framing (read first) — DIRECTIVE: pursue full production claims

User decision (2026-06-08): pursue **full production claims**, not just testnet-honest
polish. The hard guardrail: **claims must be EARNED with real backing, never asserted
ahead of the wiring.** Today the project honestly marks `production_security_claim: False`
and echo-wraps proofs (`PUBLIC_TESTNET_V0_1_16.md`, `RC1_*`). Pursuing production means
doing the REAL work to flip those — e.g. replacing the echo ZK verifier with real proving
(building on the existing RISC0/STARK guests: perps-NP, CLOB), real custody, real consensus
claims — and only then changing the flag. Flipping `production_security_claim:False`→True
without the backing is fake-green and is FORBIDDEN. Where earning a claim is out of scope,
say so; do not fake it. The biggest item (real proofs vs echo) is its own track (see below).

## Verified-good baseline (do NOT churn)

- UI builds green (`vite build` exit 0); SDK unit + contract tests pass.
- Backend is real-authority, no echo/mock at the boundary; sensitive APIs off-by-default
  with a fail-closed startup gate + deploy-profile consistency gate.
- Live-wired e2e: spot swap-exact-in, liquidity add/remove/create (in-repo file-ledger);
  perps lifecycle + zUSD mint/redeem/SP (external Tau node, behind enable-flags);
  confidential attestation; oracle; strategy; stats.
- Backend focused integration suite: 347 passed, 0 failed.
- Honest fail-closed UX: live submit refuses to fabricate a tx (except gap P0-B).

## Architecture reality (load-bearing)

The DEX is **multiple services**, not one: `api_server.py`:8000 (perps/zUSD/confidential/
autotrader/dex-quote+proof) · `tools/zeno_ledger_node.py`:8787 (spot swap/pools/liquidity/
tokenomics — the real spot authority) · oracle:9100 · external `tau-local`:65432 (perps/zUSD
settlement). Authoritative deploy = `tools/zenoctl_testnet_local/{nginx,lifecycle}.py`
(multi-upstream path routing). `.docker/nginx.conf` is a **single-upstream artifact that
strips `/api/` and cannot reach spot/oracle** — see P0-A.

---

## P0 — Integrity: real breaks + the one fake-green (fix first)

- **P0-A — Front-door routing is broken.** `.docker/nginx.conf` proxies all `/api/` to
  `:8000` with a trailing slash that strips the prefix; spot(:8787)/oracle(:9100) routes
  404. A `.docker`-based deploy has dead spot trading. FIX: replace with multi-upstream
  path routing mirroring `zenoctl_testnet_local/nginx.py`, OR clearly mark the file
  legacy/dead and document the authoritative front door. [infra/backend → Codex]
- **P0-B — Swap UI fakes finality.** `SwapInterface.jsx:297-313` flips pending→confirmed
  after a hardcoded 2200ms with no backend poll and no demo gate; demo is off in the
  shipped config, so it fires in production. FIX: poll a receipt/height/finality endpoint;
  never transition to confirmed on a timer. [UI+logic → Gemini (UX) + Codex (finality logic)]
- **P0-C — Dead fake-green UI components.** `SystemStatus.jsx` fabricates oracle/
  circuit-breaker "safety" state in live mode; both it and `TransactionHistory.jsx` stamp
  an unconditional "✓ Tau-Verified" badge. Unmounted today (not user-reachable) but latent.
  FIX: delete them. [UI → Gemini]

## P1 — Functional gaps (features that don't fully work)

- **P1-D — Sealed-bid disabled even in testnet.** `CONFIDENTIAL_SEALED_BID_API_ENABLED`
  is absent from the harness `enabled_lanes` → 404 out of the box, though the handler is
  real + fail-closed. FIX: enable it (+ state file) in the testnet profile. [config → Codex]
- **P1-E — Swap exact-out has no live settlement path.** UI `apiSwap` sends only
  `SWAP_EXACT_IN`; exact-out exists only as advisory quotes. FIX: add the exact-out
  settlement op + UI submit. [backend+UI → Codex+Gemini]
- **P1-F — Perps funding / liquidation / breaker are display-only or operator-only.**
  Funding renders "—" (not in wallet payload; no `apply_funding` route in `_ACTIONS`);
  liquidation operator-console only; `breakerActive` hardcoded false; entry price = index
  stand-in. FIX: expose funding + breaker from real market state; surface liquidation
  status; track entry price. [backend+UI → Codex+Gemini]
- **P1-G — Transaction history is session-only.** In-memory `useState([])`, no backfill,
  no persistence; reload loses it. FIX: wire a chain/explorer history read or persist.
  [backend+UI → Codex+Gemini]
- **P1-H — UI references endpoints that exist nowhere:** `/api/local-signer/sign-dex-intent`,
  `/api/confidential/attestation/verify`. FIX: implement or remove the references. [backend+UI]

## P2 — Hardening + hygiene

- **P2-I** — `_demo_auth_ok()` returns True when no token set (open-by-default); make it
  fail-closed so auth doesn't depend solely on the startup gate. [backend → Codex]
- **P2-J** — Default `ZENODEX_DEPLOY_PROFILE=production-strict` in the production image
  (D-CONFIG-002 gate is currently opt-in, unset in Dockerfile). [infra → Codex]
- **P2-K** — UI polish: nav entry for Proof Mining (currently `?tab=proofs` only); wire or
  remove dead zUSD demo buttons; browser-keygen local-testnet config must not ship to prod.
  [UI → Gemini]
- **P2-L (scope Q)** — Split routing never binds settlement (live swap submits a single-pool
  intent); quote receipts are client-self-signed not backend-issued. Bigger; confirm scope.
- **P2-M (scope Q)** — Batch-auction (A,B) engine is capable but fed one intent at a time;
  no multi-intent batch write path / UI. Confirm whether in product scope or descope.
- **P2-N** — No cheap UI regression tier (only Playwright needing the full stack). Add a
  headless smoke/component test. [test]
- **P2-O** — Doc drift: `SECURITY_POSTURE.md` cites non-existent `perps_api.py`/`zusd_api.py`.

## Execution model

Fix-agents on disjoint files, golden/characterization-first on consensus-adjacent paths,
no-git, then **Codex reviews backend/logic, Gemini reviews UI** (per user). P0 first
(integrity), then P1. P2-L/M are scope questions for the user before building.

## Decisions (user, 2026-06-08)

1. **Quality bar = pursue full production claims** (earn-not-assert; see framing above).
2. **Infra (P0-A nginx, P2-I api_server auth, P2-J deploy profile) = defer to in-flight
   work** — `api_server.py` is mid-refactor, `.docker/*` is being edited. I hand off specs,
   do not touch those files.
3. **Build split-routing→settlement** (P2-L) — promoted from "defer" to a build target.
   New consensus surface → gets a design pass before implementation.
4. **All four P1 gaps in play:** enable sealed-bid, perps funding/liquidation/breaker,
   transaction-history persistence, swap exact-out settlement.

## Execution status (live)

DONE + reviewed:
- **P0-B/P0-C** swap fake-green removal — Gemini **A/A**.
- **UI polish** (honest pending, staleness refresh→real /api/history, drawer colors/skeleton/empty,
  error humanization) — landed; **caught + neutralized an invented `explorer.tau.net` URL** (config-gated now).
- **Sealed-bid enable** — Codex **A** (fail-closed gates traced, fake-server main()=0, no escape hatches).
- **Tx-history `/api/history`** — Codex **C+** found a real cross-account leak → fixed (per-op participant
  selection + `tx_hash_v0` binding + leak-regression test) → my read confirms → **accepted**.
- **Refactor batch-3** — Codex **A/A/A−** keep + the **F** (object_package reject-order regression) fixed
  (separate schema-order table + fail-closed desync guard + double-fault corpus) → all four keep-worthy.

UNDER REVIEW:
- **Exact-out settlement (backend)** — built: `_ui_swap_tx_v0` exact-out branch (max_amount_in required,
  fail-closed, exact-in byte-identical, engine untouched); tests prove output==amount_out, input<=max,
  conservation, exceed-max→fail-closed-noop, 46 passed. Codex review in flight.

NEXT (I drive):
- **Exact-out UI** — signer parity (UI `buildAndSignSwapIntent` must reproduce the backend exact-out
  `intent_id`) + mode toggle + a JS↔Python signature-parity test. Build after the backend verdict.
- **Split-routing→settlement** — engine has the legs structure; bind the live swap (same write-path shape).

DEFERRED / OTHER LANES:
- perps funding/liquidation backend (`perps_wallet_api.py` WIP) + all infra — coordinate, hand off specs.
- **Real ZK proofs vs echo** (the production-claim keystone) — a concurrent agent owns
  `.claude/worktrees/agent-a36ba68c9141d6559/zk/state_proof_risc0/`; I do NOT collide. EARN before asserting.
