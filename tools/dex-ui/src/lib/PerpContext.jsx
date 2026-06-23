import { createContext, useContext } from 'react';

export const PerpContext = createContext(null);

export function usePerps() {
    const ctx = useContext(PerpContext);
    if (!ctx) {
        throw new Error('usePerps must be used within a PerpProvider');
    }
    return ctx;
}
