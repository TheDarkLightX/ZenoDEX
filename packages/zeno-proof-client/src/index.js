/**
 * @zenodex/proof-client — public entry point.
 *
 * Re-exports the SDK's stable surface. Consumers who only need the bundle
 * verifier should import from this module. Advanced consumers may import
 * `@zenodex/proof-client/bls` directly to pull in the BLS verifier without
 * the wallet-sync logic.
 */

export {
  BROWSER_CHECKPOINT_BUNDLE_SCHEMA_V0,
  BROWSER_WALLET_SYNC_STATE_SCHEMA_V0,
  BROWSER_CHECKPOINT_VERIFICATION_SUMMARY_SCHEMA_V0,
  hashV0,
  stableStringify,
  verifyBrowserCheckpointBundleV0,
  advanceWalletSyncStateV0,
} from './zenoProofClient.js';

export {
  verifyBlsEnvelopeV0,
  verifyBlsQuorumV0,
} from './zenoBlsVerifier.js';
