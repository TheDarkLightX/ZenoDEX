/* eslint-disable react-refresh/only-export-components */
import { createContext, useCallback, useContext, useEffect, useMemo, useState } from 'react';

export const THEMES = [
  { id: 'dark', label: 'Dark', hint: 'Original ZenoDEX brand — cyan + purple on slate.' },
  { id: 'light', label: 'Light', hint: 'Warm paper — same brand accents tuned for sunlight.' },
];

const VALID_THEME_IDS = new Set(THEMES.map((t) => t.id));
const STORAGE_KEY = 'zenodex.theme';
const DEFAULT_THEME = 'dark';

function resolveInitialTheme() {
  if (typeof window === 'undefined') return DEFAULT_THEME;
  // 1) URL ?theme=… for deep-linking a preview.
  try {
    const params = new URLSearchParams(window.location.search);
    const requested = params.get('theme');
    if (requested && VALID_THEME_IDS.has(requested)) return requested;
  } catch {
    // ignore — params parsing failures fall through to next source.
  }
  // 2) Persisted user choice.
  try {
    const stored = window.localStorage.getItem(STORAGE_KEY);
    if (stored && VALID_THEME_IDS.has(stored)) return stored;
  } catch {
    // Storage may be disabled (private mode, sandbox). Fall through.
  }
  // 3) System preference.
  try {
    if (window.matchMedia && window.matchMedia('(prefers-color-scheme: light)').matches) {
      return 'light';
    }
  } catch {
    // matchMedia unavailable (very old browser); use default.
  }
  return DEFAULT_THEME;
}

const ThemeContext = createContext({
  theme: DEFAULT_THEME,
  setTheme: () => {},
  themes: THEMES,
});

export function ThemeProvider({ children }) {
  const [theme, setThemeState] = useState(resolveInitialTheme);

  // Apply `data-theme` to <html> so CSS [data-theme="…"] selectors take.
  // We set it on <html> rather than <body> so background colors on
  // <html> + <body> both pick up the right palette.
  useEffect(() => {
    if (typeof document === 'undefined') return;
    document.documentElement.setAttribute('data-theme', theme);
  }, [theme]);

  // Persist user's explicit choice so reloads keep their selection.
  // (We do NOT auto-follow system changes once the user has chosen one,
  // matching most editor UIs — explicit > implicit.)
  const setTheme = useCallback((next) => {
    if (!VALID_THEME_IDS.has(next)) return;
    setThemeState(next);
    try {
      window.localStorage.setItem(STORAGE_KEY, next);
    } catch {
      // Storage write may fail in private/sandboxed contexts. The DOM
      // attribute still updates so the session reflects the change.
    }
  }, []);

  const value = useMemo(() => ({ theme, setTheme, themes: THEMES }), [theme, setTheme]);

  return <ThemeContext.Provider value={value}>{children}</ThemeContext.Provider>;
}

export function useTheme() {
  return useContext(ThemeContext);
}
