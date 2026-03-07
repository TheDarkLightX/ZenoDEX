export const CONFIDENTIAL_SURFACE = {
  summary: {
    title: 'Confidential Extensions',
    subtitle: 'TEE-first private execution, sealed-bid auctions, and fail-closed accounting rails.',
    verifiedAt: '2026-03-07',
  },
  checks: [
    {
      id: 'tee-gate',
      label: 'TEE Gate',
      status: 'verified',
      detail: 'Nitro / Azure attestation receipts are measured, freshness-bounded, replay-checked, and fee-conserved.',
      proof: 'ESSO verify-multi',
    },
    {
      id: 'sealed-bid-gate',
      label: 'Sealed-Bid Gate',
      status: 'verified',
      detail: 'Commit, reveal, settlement-open, empty-finalize, and no-reveal-finalize rails are cross-solver verified.',
      proof: 'ESSO verify-multi',
    },
    {
      id: 'bond-kernel',
      label: 'Bond Kernel',
      status: 'verified',
      detail: 'Refunded + slashed bonds equal total bonded, with duplicate and unknown reveal paths fail-closed.',
      proof: 'ESSO verify-multi + BVA',
    },
    {
      id: 'disaster-catalog',
      label: 'Disaster Catalog',
      status: 'green',
      detail: 'Named deadlock predecessor states collapse to a single terminating action.',
      proof: 'Exported ref replay',
    },
  ],
  phases: [
    {
      id: 'commit',
      title: 'Commit',
      detail: 'Wallet posts a commitment only. Quantity, price, and nonce stay hidden until reveal.',
    },
    {
      id: 'reveal',
      title: 'Reveal',
      detail: 'Bid opens only if commitment and nonce bind. Non-reveals lose their bond.',
    },
    {
      id: 'settle',
      title: 'Settle',
      detail: 'Uniform-price fill is deterministic and only consumes revealed units.',
    },
    {
      id: 'complete',
      title: 'Complete',
      detail: 'Empty and no-show paths now terminate explicitly instead of stalling in a control phase.',
    },
  ],
  useCases: [
    'Premium routing and risk scoring behind attested TEE sidecars',
    'Batch auctions where bids stay private until the reveal window',
    'Provider payments with replay-sensitive receipts and bounded attestation age',
  ],
  disasterCatalog: [
    {
      disasterId: 'empty_auction_deadlock',
      model: 'sealed_bid_commit_reveal_gate_v1',
      dischargeAction: 'finalize_empty_auction',
      status: 'closed',
    },
    {
      disasterId: 'no_reveal_deadlock',
      model: 'sealed_bid_commit_reveal_gate_v1',
      dischargeAction: 'finalize_no_reveal_auction',
      status: 'closed',
    },
    {
      disasterId: 'empty_bond_deadlock',
      model: 'sealed_bid_non_reveal_bond_v1',
      dischargeAction: 'finalize_empty_bonds',
      status: 'closed',
    },
  ],
};
