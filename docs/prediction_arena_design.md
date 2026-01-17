# Prediction Arena: Multi-Player DEX Game

## Overview

A prediction game where 2-16 players (humans + AI agents) compete to predict market price movements, with rewards from staked tokens and DEX trading fees.

## AI Agent Roles

| Role | Function | Skin in Game |
|------|----------|--------------|
| 🤖 **Predictor Agent** | Competes alongside humans using ML models | Yes - stakes tokens like humans |
| 🔮 **Oracle Agent** | Provides authoritative price outcome data | Bonded - slashed for incorrect data |
| 🏠 **House Agent** | Manages LP pool contributions to prize | N/A - represents protocol |
| ⚖️ **Arbiter Agent** | Verifies commit-reveal integrity | Bonded - governance-appointed |

## Game Flow

```
┌──────────────────────────────────────────────────────────────┐
│                    PREDICTION ARENA                          │
├──────────────────────────────────────────────────────────────┤
│                                                               │
│  ┌─────────────┐    ┌─────────────┐    ┌─────────────┐       │
│  │  RECRUITING │───▶│  COMMITTING │───▶│  REVEALING  │       │
│  │ (2-16 join) │    │ (all commit)│    │ (all reveal)│       │
│  └─────────────┘    └─────────────┘    └─────────────┘       │
│         │                                      │              │
│         │                                      ▼              │
│         │                              ┌─────────────┐       │
│         │                              │  RESOLVING  │       │
│         │                              │  (oracle)   │       │
│         │                              └─────────────┘       │
│         │                                      │              │
│         ▼                                      ▼              │
│  ┌─────────────┐                       ┌─────────────┐       │
│  │  CANCELLED  │                       │   PAYING    │       │
│  │  (refunds)  │                       │  (winners)  │       │
│  └─────────────┘                       └─────────────┘       │
│                                                               │
└──────────────────────────────────────────────────────────────┘
```

## Game Modes

1. **Classic** (mode=1): Simple Up/Down/Flat prediction
2. **Advanced** (mode=2): Price range brackets (A/B/C)
3. **Expert** (mode=3): Exact price target within tolerance

## Payout Structure

- **Solo Winner**: Takes entire prize pool
- **Multiple Winners**: Proportional to stake weight
- **No Winners**: House (LP pool) takes all
- **House Edge**: 5% (configurable) goes to LPs regardless

## Key Invariants

- `PayoutConservation`: Never pay more than prize pool
- `PlayerCountConsistency`: humans + AI = total players
- `MinimumPlayersEnforced`: Can't start with < min_players
- `RevealsCannotExceedCommits`: Commit-reveal integrity
