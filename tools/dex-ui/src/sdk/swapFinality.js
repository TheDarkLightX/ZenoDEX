// Copyright (c) DarkLightX/Dana Edwards. All rights reserved.

function nonemptyString(value) {
  return typeof value === 'string' && value.trim().length > 0 ? value.trim() : '';
}

export function extractReceiptHash(receipt) {
  if (!receipt || typeof receipt !== 'object') return '';
  return nonemptyString(receipt.receipt_hash)
    || nonemptyString(receipt.receiptHash)
    || nonemptyString(receipt.body?.receipt_hash)
    || nonemptyString(receipt.body?.receiptHash);
}

export function deriveSwapFinality(maybeRemote = {}) {
  const remote = maybeRemote && typeof maybeRemote === 'object' ? maybeRemote : {};
  const receipt = remote.receipt && typeof remote.receipt === 'object' ? remote.receipt : null;
  const txAccepted = remote.tx_accepted === true;
  const receiptAccepted = receipt?.accepted === true;
  const accepted = txAccepted || receiptAccepted;
  const txHashRaw = remote.txHash || remote.tx_hash || '';

  return {
    accepted,
    status: accepted ? 'confirmed' : 'pending',
    txHash: nonemptyString(txHashRaw) || (txHashRaw ? String(txHashRaw) : ''),
    height: remote.height ?? null,
    receipt,
    receiptHash: extractReceiptHash(receipt),
    acceptanceEvidence: receiptAccepted
      ? 'receipt.accepted=true'
      : (txAccepted ? 'tx_accepted=true' : ''),
  };
}
