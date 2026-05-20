import { createContext, useContext } from 'react';

export const DemoModeContext = createContext({
    demoMode: true,
    setDemoMode: () => { },
});

export function useDemoMode() {
    return useContext(DemoModeContext);
}
