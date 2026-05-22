/**
 * Deterministic route profile catalog and selectors.
 *
 * Profiles map UX intents to explicit routing gate policies.
 */

export const ROUTE_PROFILES = {
    latency: {
        id: 'latency',
        label: 'Latency',
        policy: 'stress_or_pressure_adaptive',
        config: {
            stress_threshold: 0.4,
            pressure_threshold: 1.6,
            pressure_slope: 1.2,
        },
        description: 'Lowest quote compute cost; accepts a small quality loss.',
    },
    balanced: {
        id: 'balanced',
        label: 'Balanced',
        policy: 'stress_or_pressure_tripiece',
        config: {
            stress_threshold: 0.4,
            tripiece_stress_lower_cutoff: 0.14,
            tripiece_stress_upper_cutoff: 0.2,
            tripiece_pressure_mid_band: 1.6,
            tripiece_pressure_upper_band: 1.45,
            tripiece_pressure_low_base: 2.3,
            tripiece_fee_slope: 16.0,
        },
        description: 'Default profile: near-quality capture with moderate compute.',
    },
    quality: {
        id: 'quality',
        label: 'Quality',
        policy: 'stress_or_pressure_piecewise_fee',
        config: {
            stress_threshold: 0.4,
            fee_piecewise_stress_cutoff: 0.12,
            fee_piecewise_pressure_mid: 1.5,
            fee_piecewise_pressure_low: 2.3,
            fee_piecewise_fee_slope: 12.0,
        },
        description: 'Prioritizes value capture; still bounded versus always-two-hop.',
    },
};

const PROFILE_ORDER = ['latency', 'balanced', 'quality'];

export function getProfileById(profileId) {
    return ROUTE_PROFILES[profileId] || ROUTE_PROFILES.balanced;
}

export function profileFromSlider(sliderValue) {
    const clamped = Math.max(0, Math.min(100, Number(sliderValue) || 0));
    if (clamped <= 33) return ROUTE_PROFILES.latency;
    if (clamped <= 66) return ROUTE_PROFILES.balanced;
    return ROUTE_PROFILES.quality;
}

export function sliderValueForProfile(profileId) {
    if (profileId === 'latency') return 20;
    if (profileId === 'quality') return 80;
    return 50;
}

/**
 * Deterministic "set-and-forget" profile selection based on observed regime.
 */
export function deriveAutoProfile({ stress = 0, pressure = 0, priceImpact = 0 }) {
    if (stress >= 0.25 || priceImpact >= 0.05 || pressure >= 2.4) {
        return ROUTE_PROFILES.quality;
    }
    if (stress <= 0.08 && priceImpact <= 0.008 && pressure <= 1.8) {
        return ROUTE_PROFILES.latency;
    }
    return ROUTE_PROFILES.balanced;
}

export function listRouteProfiles() {
    return PROFILE_ORDER.map((profileId) => ROUTE_PROFILES[profileId]);
}
