# ZenoDEX A-Grade Remediation Plan

Date: 2026-06-07

This plan turns the codebase review into a prioritized execution path. It starts
with high-leverage guardrails that are cheap to land and then progresses toward
mainnet-grade trust minimization.

## Target Grades

| Area | Current risk | A-grade exit criterion |
| --- | --- | --- |
| Assurance | Historical lanes are strong, but live replay depends on external/private tooling. | Clean-machine replay publishes signed receipts for critical, release, proof, Tau, dependency, and container lanes. |
| Production readiness | Public-testnet candidate, not mainnet-closed. | Full production gate passes on a fresh machine, plus two-machine/latest-main network evidence and incident drills. |
| Code quality | Large functions and high cyclomatic complexity hotspots. | No new function exceeds complexity 5 or 60 lines; legacy baseline burns down every release. |
| Decentralization | Trust-minimization target remains `frontier_open`. | Every value-moving transition is deterministic-replay accepted or zkVM-receipt accepted; unsupported profiles fail closed. |
| Security | Strong fail-closed posture, but UI audit/proof tooling can be environment-sensitive. | Dependency and image audits are reproducible from pinned mirrors or checked fallback attestations. |

## Phase 0: Easy, High-Impact Wins

1. **Install a complexity ratchet.** The new `tools/check_complexity_ratchet.py`
   blocks complexity regressions against the committed baseline while allowing a
   controlled burn-down of legacy hotspots.
2. **Gate it in production readiness.** `tools/prod_gate.sh` now runs the
   complexity ratchet before proof and test lanes, so new production candidates
   cannot silently increase complexity debt.
3. **Make optional PBT dependencies fail cleanly.** Property-test modules that
   require Hypothesis should skip at collection when Hypothesis is absent, while
   full gates continue to install locked dev requirements.
4. **Publish a top-20 hotspot refactor queue.** Use the ratchet JSON output to
   assign owners and convert each large handler into small pure functions,
   validators, and command objects.

## Phase 1: Code Quality Burn-Down

- Refactor `src/integration/api_server.py::_maybe_handle_dex_api` into one route
  table plus one command handler per API family.
- Refactor settlement validators into composable rule objects:
  `IntentSetRule`, `FillCompletenessRule`, `WitnessBindingRule`,
  `DeltaReplayRule`, and `ConservationRule`.
- Add CI mode `python tools/check_complexity_ratchet.py --strict` for touched
  files first, then expand to all non-deprecated source.
- Require DbC docstrings for consensus-critical public functions:
  preconditions, invariants, and postconditions.

## Phase 2: Assurance Reproducibility

- Build a public clean-room replay container that can run critical gates without
  private paths.
- For private ESSO lanes, publish hash-bound receipts plus verifier metadata and
  a documented challenge procedure.
- Add a CI artifact that captures `permissionless_assurance.py status`, kernel
  receipts, Tau syntax/trace summaries, and dependency/image audit reports.
- Treat missing audit endpoints as release-blocking unless a pinned mirror or
  prior signed advisory snapshot is used.

## Phase 3: Mainnet Production Closure

- Run and archive a two-machine latest-main rehearsal with validator restarts,
  peer churn, malformed transaction floods, and snapshot recovery.
- Close the trust-minimization open surfaces in priority order:
  1. oracle critical actions,
  2. UPBA batch clearing,
  3. zUSD lifecycle,
  4. perps settlement,
  5. proof-market rewards,
  6. recursive epoch aggregation,
  7. light-client checkpoint quorum.
- Require quorum/finality evidence for public checkpoints and ensure proof
  journals bind pre-state root, post-state root, transaction commitment, nonce
  roots, and receipt roots.

## Phase 4: Security Hardening Beyond the Current Gate

- Add custom seccomp only after syscall trace replay for Python, nginx, DNS,
  TLS, and health checks.
- Add request-body size, array-length, and object-depth caps to every API
  boundary that accepts JSON.
- Add fuzz/PBT suites for malformed receipts, duplicate intent/fill IDs,
  maximum-domain arithmetic, and adversarial route splits.
- Add supply-chain fallback attestations for npm and Trivy so release gates do
  not depend on a single external endpoint at release time.

## Operating Rule

Every release must either improve at least one ratcheted metric or explicitly
carry a time-bounded exception. No exception may weaken fail-closed settlement,
nonce coverage, replay/proof binding, or dependency hash-locking.
