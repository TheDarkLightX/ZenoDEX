/**
 * Quote certificate helpers (client-side fail-closed verification).
 *
 * The certificate is deterministic over a canonical quote payload.
 */

function roundNum(value, decimals = 10) {
    if (!Number.isFinite(value)) return 0;
    const scale = 10 ** decimals;
    return Math.round(value * scale) / scale;
}

function canonicalPayload(payload) {
    return {
        version: 1,
        fromSymbol: String(payload.fromSymbol || ''),
        toSymbol: String(payload.toSymbol || ''),
        amountIn: roundNum(Number(payload.amountIn || 0)),
        amountOut: roundNum(Number(payload.amountOut || 0)),
        minOutput: roundNum(Number(payload.minOutput || 0)),
        slippageBps: Number(payload.slippageBps || 0),
        routePath: String(payload.routePath || ''),
        routeType: String(payload.routeType || ''),
        profileId: String(payload.profileId || ''),
        policy: String(payload.policy || ''),
        quoteCallCount: Number(payload.quoteCallCount || 0),
    };
}

function canonicalString(payload) {
    const c = canonicalPayload(payload);
    return [
        c.version,
        c.fromSymbol,
        c.toSymbol,
        c.amountIn.toFixed(10),
        c.amountOut.toFixed(10),
        c.minOutput.toFixed(10),
        c.slippageBps,
        c.routePath,
        c.routeType,
        c.profileId,
        c.policy,
        c.quoteCallCount,
    ].join('|');
}

// FNV-1a 32-bit (deterministic, fast, non-cryptographic integrity tag)
function fnv1a32(input) {
    let h = 0x811c9dc5;
    for (let i = 0; i < input.length; i += 1) {
        h ^= input.charCodeAt(i);
        h = Math.imul(h, 0x01000193) >>> 0;
    }
    return h.toString(16).padStart(8, '0');
}

export function createQuoteCertificate(payload, { nowMs = Date.now(), ttlMs = 25000 } = {}) {
    const canonical = canonicalPayload(payload);
    const payloadHash = fnv1a32(canonicalString(canonical));
    const issuedAtMs = Number(nowMs);
    const expiresAtMs = issuedAtMs + Math.max(1000, Number(ttlMs));
    return {
        version: 1,
        issuedAtMs,
        expiresAtMs,
        payloadHash,
        payload: canonical,
    };
}

export function verifyQuoteCertificate(certificate, payload, { nowMs = Date.now() } = {}) {
    if (!certificate || typeof certificate !== 'object') {
        return { ok: false, reason: 'missing_certificate', remainingMs: 0 };
    }
    if (!certificate.payload || !certificate.payloadHash) {
        return { ok: false, reason: 'malformed_certificate', remainingMs: 0 };
    }

    const now = Number(nowMs);
    if (now > Number(certificate.expiresAtMs || 0)) {
        return { ok: false, reason: 'certificate_expired', remainingMs: 0 };
    }

    const certPayloadHash = fnv1a32(canonicalString(certificate.payload));
    if (certPayloadHash !== certificate.payloadHash) {
        return { ok: false, reason: 'certificate_payload_tampered', remainingMs: 0 };
    }

    const livePayload = canonicalPayload(payload);
    const livePayloadHash = fnv1a32(canonicalString(livePayload));
    if (livePayloadHash !== certificate.payloadHash) {
        return { ok: false, reason: 'quote_mismatch', remainingMs: 0 };
    }

    return {
        ok: true,
        reason: 'ok',
        remainingMs: Math.max(0, Number(certificate.expiresAtMs) - now),
    };
}
