// Copyright (c) DarkLightX/Dana Edwards. All rights reserved.

export function createMockTxHash() {
    const bytes = new Uint8Array(32);
    if (typeof globalThis !== 'undefined' && globalThis.crypto?.getRandomValues) {
        globalThis.crypto.getRandomValues(bytes);
    } else {
        for (let i = 0; i < bytes.length; i += 1) {
            bytes[i] = Math.floor(Math.random() * 256);
        }
    }
    const hex = Array.from(bytes, (byte) => byte.toString(16).padStart(2, '0')).join('');
    return `0x${hex}`;
}

export function shortHash(hash) {
    if (!hash) return '';
    return `${hash.slice(0, 10)}...${hash.slice(-8)}`;
}

export function clamp(value, lo, hi) {
    return Math.min(hi, Math.max(lo, value));
}

export function estimateRoutePendingVolumes({ amountIn, routeType, profileId, gateDecision, hopOutputs = [] }) {
    const baseByProfile = {
        latency: 0.04,
        balanced: 0.10,
        quality: 0.16,
        legacy: 0.06,
    };
    const base = baseByProfile[String(profileId || '').toLowerCase()] ?? 0.10;
    const stress = clamp(Number(gateDecision?.stress ?? 0), 0, 2);
    const pressure = clamp(Number(gateDecision?.pressure ?? 1), 0, 4);
    const gateBoost = gateDecision?.considerTwoHop ? 0.03 : 0;
    const multiplier = base + gateBoost;
    const scale = 1 + (0.35 * stress) + (0.2 * Math.max(0, pressure - 1));

    const pending1 = Math.max(0, Math.round(Number(amountIn || 0) * multiplier * scale));
    if (String(routeType) !== 'two-hop') {
        return [pending1];
    }

    const hopInput2 = Math.max(0, Number(hopOutputs?.[0] ?? 0));
    const pending2 = Math.max(0, Math.round(hopInput2 * multiplier * 0.8 * scale));
    return [pending1, pending2];
}
