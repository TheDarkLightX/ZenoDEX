// Type declarations for @zenodex/proof-client.
// Hand-written to keep zero runtime cost — no TypeScript build step.

export const BROWSER_CHECKPOINT_BUNDLE_SCHEMA_V0: 'zenodex.zeno_sdk.browser_checkpoint_bundle.v0';
export const BROWSER_WALLET_SYNC_STATE_SCHEMA_V0: 'zenodex.zeno_sdk.wallet_sync_state.v0';
export const BROWSER_CHECKPOINT_VERIFICATION_SUMMARY_SCHEMA_V0: 'zenodex.zeno_sdk.browser_checkpoint_verification_summary.v0';
export const ZK_PROOF_STATUS_SUMMARY_SCHEMA_V0: 'zenodex.zeno_sdk.zk_proof_status_summary.v0';

/** Canonical JSON serialization (sort_keys, no floats, no surrogates). */
export function stableStringify(value: unknown): string;

/** Domain-separated SHA-256 mirroring `src/integration/zeno_ledger_v0.py::hash_v0`. */
export function hashV0(domain: string, value: unknown | Uint8Array): Promise<string>;

export type ZkProofMode = 'strict' | 'fixture' | 'fallback' | 'open' | 'rejected';

export interface ZkProofStatusSummary {
  schema: 'zenodex.zeno_sdk.zk_proof_status_summary.v0';
  ok: boolean;
  status: 'accepted' | 'blocked';
  proof_mode: ZkProofMode;
  zk_mode_requested?: 'auto-strict' | 'strict' | 'open' | null;
  zk_mode_effective?: 'strict' | 'open' | null;
  zk_required: boolean;
  proof_verifier_kind?: 'disabled' | 'subprocess' | 'misconfigured' | null;
  proof_artifact_hashes: Record<string, string>;
  expected_proof_artifact_hashes: Record<string, string>;
  artifact_pinning_verified: boolean;
  fallback: boolean;
  fallback_reason: string | null;
  fixture_backed: boolean;
  production_security_claim: boolean;
  can_make_production_security_claim: boolean;
  gaps: string[];
}

export interface ParseZkProofStatusOptions {
  /** Caller-pinned verifier/circuit/image hashes. A mismatch makes the status fail closed. */
  expectedProofArtifactHashes?: Record<string, string>;
  /** Snake-case alias for JSON-loaded option bags. */
  expected_proof_artifact_hashes?: Record<string, string>;
}

export function parseZkProofStatusV0(input: unknown, options?: ParseZkProofStatusOptions): ZkProofStatusSummary;

export interface VerifyBundleOptions {
  /** Header hash/root the first bundle header must extend. This must come from caller trust state, not the bundle. */
  expectedTrustedPrevHeaderHash: string;
  /** Pinned signer-registry hash expected by the caller. This must not be learned from the same bundle. */
  expectedSignerRegistryHash: string;
  /**
   * When true, every BLS envelope is cryptographically verified in-browser
   * using `@noble/curves`. The browser no longer needs to trust the builder's
   * `python_bls_quorum_verified` flag.
   */
  requireIndependentBls?: boolean;
  /** Explicit weaker mode for fixtures or already trusted builders. */
  trustBuilderBls?: boolean;
}

export interface VerifyBundleSuccess {
  ok: true;
  status: 'accepted' | 'accepted_with_builder_bls_trust';
  trust_model: 'independent_bls' | 'builder_bls_claim';
  bundle_hash: string;
  chain_id: string;
  height: number;
  checkpoint_hash: string;
  target_header_hash: string;
  trusted_prev_header_hash: string;
  signer_registry_hash: string;
  browser_range_replay_verified: true;
  browser_range_last_header_hash: string;
  browser_bls_quorum_verified: boolean;
  browser_bls_accepted_weight: number | null;
  builder_bls_quorum_verified: true;
  gaps: string[];
}

export interface VerifyBundleFailure {
  ok: false;
  status: 'rejected';
  gaps: string[];
  browser_bls_quorum_verified: false;
  builder_bls_quorum_verified: false;
}

export type VerifyBundleResult = VerifyBundleSuccess | VerifyBundleFailure;

export function verifyBrowserCheckpointBundleV0(
  bundle: unknown,
  options?: VerifyBundleOptions,
): Promise<VerifyBundleResult>;

export interface WalletSyncState {
  schema: 'zenodex.zeno_sdk.wallet_sync_state.v0';
  surface: string;
  chain_id: string;
  height: number;
  app_hash: string;
  target_header_hash: string;
  checkpoint_hash: string;
  signer_registry_hash: string;
  trust_model: 'independent_bls' | 'builder_bls_claim';
  bundle_hash: string;
  updated_at_ms: number;
  state_hash: string;
}

export interface AdvanceWalletSyncStateOptions {
  currentState?: WalletSyncState | null;
  bundle: unknown;
  surface?: string;
  updatedAtMs?: number;
  requireIndependentBls?: boolean;
  trustBuilderBls?: boolean;
  expectedTrustedPrevHeaderHash?: string | null;
  expectedSignerRegistryHash?: string | null;
}

export interface AdvanceWalletSyncStateSuccess {
  ok: true;
  status: 'accepted' | 'accepted_with_builder_bls_trust';
  state: WalletSyncState;
  verification: VerifyBundleSuccess;
}

export interface AdvanceWalletSyncStateFailure {
  ok: false;
  status: 'rejected';
  gaps: string[];
}

export function advanceWalletSyncStateV0(
  options: AdvanceWalletSyncStateOptions,
): Promise<AdvanceWalletSyncStateSuccess | AdvanceWalletSyncStateFailure>;

export interface VerifyEnvelopeOptions {
  expectedPayloadKind?: string;
  expectedPayloadHash?: string;
}

export interface VerifyEnvelopeSuccess {
  ok: true;
  envelopeHash: string;
}

export interface VerifyEnvelopeFailure {
  ok: false;
  error: string;
}

export function verifyBlsEnvelopeV0(
  envelope: unknown,
  options?: VerifyEnvelopeOptions,
): Promise<VerifyEnvelopeSuccess | VerifyEnvelopeFailure>;

export interface VerifyQuorumOptions {
  expectedPayloadHash?: string;
}

export interface AcceptedSigner {
  signer_id: string;
  key_id: string;
  weight: number;
}

export interface AcceptedSignature extends AcceptedSigner {
  envelope_hash: string;
}

export interface VerifyQuorumSuccess {
  ok: true;
  acceptedWeight: number;
  threshold: number;
  acceptedSigners: AcceptedSigner[];
  acceptedSignatures: AcceptedSignature[];
  quorumReportHash: string;
  payloadKind: string;
  payloadHash: string;
}

export interface VerifyQuorumFailure {
  ok: false;
  error: string;
  accepted?: AcceptedSigner[];
  acceptedWeight?: number;
  threshold?: number;
}

export function verifyBlsQuorumV0(
  bundle: unknown,
  options?: VerifyQuorumOptions,
): Promise<VerifyQuorumSuccess | VerifyQuorumFailure>;
