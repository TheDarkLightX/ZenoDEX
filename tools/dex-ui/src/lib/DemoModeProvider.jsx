import { useCallback, useState } from 'react';
import { DemoModeContext } from './DemoModeContext.jsx';

function getRuntimeConfigDemoMode() {
    if (typeof window === 'undefined') {
        return undefined;
    }
    const raw = window.__ZENODEX_CONFIG__;
    if (!raw || typeof raw !== 'object' || raw.demoMode === undefined) {
        return undefined;
    }
    return raw.demoMode === true || raw.demoMode === 'true';
}

function getInitialDemoMode() {
    if (typeof window !== 'undefined') {
        // 1. Check URL param (highest priority for testing)
        const urlParams = new URLSearchParams(window.location.search);
        if (urlParams.has('demo')) {
            return urlParams.get('demo') === 'true';
        }
    }

    // 2. Check localStorage (user preference)
    try {
        const stored = localStorage.getItem('zenodex-demo-mode');
        if (stored !== null) {
            return stored === 'true';
        }
    } catch {
        // Ignore storage failures (private mode, locked down browser).
    }

    // 3. Check runtime config (works for IPFS / static hosting without rebuilds)
    const runtimeDemoMode = getRuntimeConfigDemoMode();
    if (runtimeDemoMode !== undefined) {
        return runtimeDemoMode;
    }

    // 4. Check environment variable (Vite)
    if (typeof import.meta !== 'undefined' && import.meta.env?.VITE_DEMO_MODE !== undefined) {
        return import.meta.env.VITE_DEMO_MODE === 'true';
    }

    // 5. Default: demo mode ON for safety (no accidental mainnet interactions)
    return true;
}

export function DemoModeProvider({ children }) {
    const [demoMode, setDemoModeState] = useState(getInitialDemoMode);

    const setDemoMode = useCallback((value) => {
        const next = Boolean(value);
        setDemoModeState(next);
        try {
            localStorage.setItem('zenodex-demo-mode', next.toString());
        } catch {
            // Ignore storage failures (demo mode still works for the session).
        }
    }, []);

    return (
        <DemoModeContext.Provider value={{ demoMode, setDemoMode }}>
            {children}
        </DemoModeContext.Provider>
    );
}
