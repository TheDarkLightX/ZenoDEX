# ZenoDex TestNet Integration Guide

This document outlines what's needed to connect ZenoDex to Tau Net Alpha (TestNet).

## Current State

| Component | Status | Notes |
|-----------|--------|-------|
| **Deterministic Kernels** | ✅ Verified | CPMM, LP, Oracle, Vault, Fee Distribution |
| **Tau Specs** | ✅ 130+ Complete | Core DEX, tokenomics, governance |
| **GUI** | ✅ TestNet-Ready | AGRS/ZDEX branding, client-side CPMM |

## Integration Checklist

### 1. Wallet Connection
```javascript
// Replace mock wallet in WalletConnect.jsx
import { TauProvider } from '@tau/sdk'; // When available

const connectWallet = async () => {
  const provider = new TauProvider('wss://alpha.tau.net');
  const address = await provider.connect();
  return { address, provider };
};
```

### 2. Pool State
```javascript
// Replace MOCK_POOLS in SwapInterface.jsx
const fetchPools = async (provider) => {
  // Query on-chain state for pool reserves
  const state = await provider.queryState('pools');
  return parsePoolState(state);
};
```

### 3. Transaction Submission
```javascript
// Hook into swap execution
const submitSwap = async (provider, swap) => {
  const intent = {
    from_token: swap.fromToken,
    to_token: swap.toToken,
    amount_in: swap.amountIn,
    min_out: swap.minOutput,
    deadline: Date.now() + 300000, // 5 min
  };
  
  // Sign and submit to P2P network
  const signed = await provider.signIntent(intent);
  return provider.submitIntent(signed);
};
```

### 4. Tau Validation
```javascript
// Optionally validate locally before submit
import { validateSwap } from './lib/validation';

// Then on-chain via Tau specs:
// swap_exact_in_v1.tau validates the settlement
```

## Architecture

```
┌────────────────────────────────┐
│         ZenoDex GUI            │
│  (React + Client-side CPMM)    │
└───────────────┬────────────────┘
                │ Sign & Submit
                ▼
┌────────────────────────────────┐
│       Tau Net Alpha            │
│  (P2P Intent Propagation)      │
└───────────────┬────────────────┘
                │ Validate
                ▼
┌────────────────────────────────┐
│        Tau Specs               │
│  (swap_exact_in_v1.tau, etc.)  │
└───────────────┬────────────────┘
                │ Execute
                ▼
┌────────────────────────────────┐
│     Deterministic Kernels      │
│  (Verified state transitions)  │
└────────────────────────────────┘
```

## Files to Update

| File | Change |
|------|--------|
| `components/WalletConnect.jsx` | Real wallet SDK |
| `components/SwapInterface.jsx` | Live pool queries |
| `lib/cpmm.js` | Keep (client-side preview) |
| `lib/validation.js` | Keep (UX validation) |

## Environment Variables

```bash
# .env when TestNet is live
VITE_TAU_RPC=wss://alpha.tau.net
VITE_CHAIN_ID=tau-alpha
```

## Testing with TestNet

```bash
cd tools/dex-ui
npm run dev

# TestNet faucet (when available)
curl -X POST https://faucet.tau.net/drip -d '{"address":"YOUR_BLS_PUBKEY"}'
```

## Dependencies to Add

```json
{
  "@tau/sdk": "^0.1.0",
  "@tau/wallet-adapter": "^0.1.0"
}
```

> These packages will be available when Tau Net Alpha launches.
