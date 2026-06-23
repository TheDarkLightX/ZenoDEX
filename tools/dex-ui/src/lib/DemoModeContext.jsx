import { createContext, useContext } from 'react';

export const DemoModeContext = createContext({
    demoMode: false,
    setDemoMode: () => { },
});

export function useDemoMode() {
    return useContext(DemoModeContext);
}
