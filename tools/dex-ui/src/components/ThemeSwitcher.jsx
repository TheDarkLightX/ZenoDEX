import { useTheme } from '../lib/ThemeContext.jsx';
import './ThemeSwitcher.css';

/**
 * Single-button toggle between Dark and Light. Shows the *target* theme's
 * icon — i.e. if you're in Dark, the button shows the sun (click → go to
 * Light). Matches the convention in GitHub, Linear, Vercel, etc. Keeps
 * the header compact (one icon, no labels).
 */
function ThemeSwitcher() {
  const { theme, setTheme } = useTheme();
  const isDark = theme !== 'light';
  const nextTheme = isDark ? 'light' : 'dark';
  const label = isDark ? 'Switch to light theme' : 'Switch to dark theme';

  return (
    <button
      type="button"
      className="theme-toggle"
      onClick={() => setTheme(nextTheme)}
      title={label}
      aria-label={label}
    >
      {isDark ? <SunIcon /> : <MoonIcon />}
    </button>
  );
}

function SunIcon() {
  return (
    <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor"
      strokeWidth="2" strokeLinecap="round" strokeLinejoin="round" aria-hidden="true">
      <circle cx="12" cy="12" r="4" />
      <path d="M12 2v2M12 20v2M4.93 4.93l1.41 1.41M17.66 17.66l1.41 1.41M2 12h2M20 12h2M4.93 19.07l1.41-1.41M17.66 6.34l1.41-1.41" />
    </svg>
  );
}

function MoonIcon() {
  return (
    <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor"
      strokeWidth="2" strokeLinecap="round" strokeLinejoin="round" aria-hidden="true">
      <path d="M21 12.79A9 9 0 1 1 11.21 3 7 7 0 0 0 21 12.79z" />
    </svg>
  );
}

export default ThemeSwitcher;
