// swapFinality.js — pure derivation of swap finality from the live /api/swap response.
//
// No-fake-green contract: the ledger returns acceptance SYNCHRONOUSLY in the swap
// response. A swap is reported 'confirmed' ONLY when the response actually carries
// an acceptance flag (`tx_accepted === true` or `receipt.accepted === true`). Every
// other accepted-but-unproven case stays 'pending' (honest). There is NO timer or
// optimistic auto-confirm: finality is never fabricated for a swap the ledger did
// not accept.
//
// This module is intentionally dependency-free so the SDK test tier
// (node:test, src/sdk/*.test.mjs) can import it without pulling in React.

/**
 * Interpret a remote /api/swap response into a finality decision.
 *
 * Throws (preserving the existing call-site catch behaviour) when the response
 * explicitly reports rejection (`ok === false`). The thrown message matches the
 * legacy inline check so the surrounding try/catch handles it verbatim.
 *
 * @param {object|null|undefined} maybeRemote Raw response object from apiSwap.
 * @returns {{ accepted: boolean, status: 'confirmed'|'pending', txHash: string, height: (number|null), receipt: (object|null) }}
 */
export function deriveSwapFinality(maybeRemote) {
  if (maybeRemote && maybeRemote.ok === false) {
    throw new Error(maybeRemote.error || 'swap_rejected');
  }

  const receipt = (maybeRemote && maybeRemote.receipt) || null;
  // Acceptance must be asserted by the ledger response. Absence => pending, never confirmed.
  const accepted = maybeRemote?.tx_accepted === true || receipt?.accepted === true;

  const rawHash = maybeRemote?.txHash || maybeRemote?.tx_hash;
  // Keep txHash falsy ('') when absent so the call site's missing-hash branch still fires.
  const txHash = rawHash ? String(rawHash) : '';

  const height = maybeRemote?.height ?? null;

  return {
    accepted,
    status: accepted ? 'confirmed' : 'pending',
    txHash,
    height,
    receipt,
  };
}
