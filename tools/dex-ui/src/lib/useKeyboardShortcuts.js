import { useEffect, useRef } from 'react';

/**
 * useKeyboardShortcuts — centralised keyboard shortcut hook.
 *
 * Registers shortcuts described by a map of accelerator strings to handlers.
 * Accelerator syntax (case-insensitive):
 *   "s"            -> plain key S
 *   "alt+s"        -> Alt + S
 *   "ctrl+s"       -> Ctrl + S (also matches Cmd+S on macOS)
 *   "shift+/"      -> Shift + /  (i.e. "?")
 *   "enter"        -> Enter key
 *   "escape"       -> Escape key
 *
 * Shortcuts are ignored when the active element is an input, textarea, or
 * contenteditable host — UNLESS the shortcut explicitly includes the modifier
 * (alt/ctrl/meta), in which case it fires regardless (so Alt+1 works while
 * typing in an amount field).
 *
 * @param {Record<string, (e: KeyboardEvent) => void>} shortcuts
 * @param {object} [opts]
 * @param {boolean} [opts.enabled=true]
 */
export function useKeyboardShortcuts(shortcuts, opts = {}) {
  const shortcutsRef = useRef(shortcuts);
  useEffect(() => {
    shortcutsRef.current = shortcuts;
  });

  const { enabled = true } = opts;

  useEffect(() => {
    if (!enabled) return;

    const handler = (e) => {
      const map = shortcutsRef.current;
      if (!map) return;

      const accel = acceleratorFromEvent(e);
      if (!accel) return;

      // Check exact match first, then wildcard modifier matches
      const fn = map[accel] ?? map[accel.split('+').pop()];
      if (!fn) return;

      // Don't fire plain-key shortcuts when typing in a field
      const el = e.target;
      const isTyping =
        el &&
        (el.tagName === 'INPUT' ||
          el.tagName === 'TEXTAREA' ||
          el.isContentEditable === true);
      const hasModifier = e.altKey || e.ctrlKey || e.metaKey;
      if (isTyping && !hasModifier) return;

      e.preventDefault();
      fn(e);
    };

    window.addEventListener('keydown', handler);
    return () => window.removeEventListener('keydown', handler);
  }, [enabled]);
}

/**
 * Build a canonical accelerator string from a KeyboardEvent.
 * Returns e.g. "alt+s", "ctrl+enter", "shift+/", or null if the key is
 * a pure modifier press.
 */
function acceleratorFromEvent(e) {
  const key = e.key.toLowerCase();
  // Ignore standalone modifier presses
  if (['alt', 'control', 'meta', 'shift'].includes(key)) return null;

  const parts = [];
  if (e.altKey) parts.push('alt');
  if (e.ctrlKey || e.metaKey) parts.push('ctrl');
  if (e.shiftKey) parts.push('shift');
  parts.push(key);
  return parts.join('+');
}

/**
 * useFocusTrap — trap focus within a container while active.
 *
 * @param {React.RefObject<HTMLElement>} containerRef
 * @param {boolean} active
 */
export function useFocusTrap(containerRef, active) {
  useEffect(() => {
    if (!active || !containerRef.current) return;

    const container = containerRef.current;
    const previouslyFocused = document.activeElement;

    // Focus the container or first focusable element
    const focusables = getFocusables(container);
    if (focusables.length > 0) {
      focusables[0].focus();
    } else {
      container.focus();
    }

    const handler = (e) => {
      if (e.key !== 'Tab') return;
      const items = getFocusables(container);
      if (items.length === 0) return;
      const first = items[0];
      const last = items[items.length - 1];
      if (e.shiftKey && document.activeElement === first) {
        e.preventDefault();
        last.focus();
      } else if (!e.shiftKey && document.activeElement === last) {
        e.preventDefault();
        first.focus();
      }
    };

    container.addEventListener('keydown', handler);
    return () => {
      container.removeEventListener('keydown', handler);
      if (previouslyFocused && previouslyFocused.focus) {
        previouslyFocused.focus();
      }
    };
  }, [containerRef, active]);
}

function getFocusables(container) {
  const selector =
    'a[href], button:not([disabled]), input:not([disabled]), select:not([disabled]), textarea:not([disabled]), [tabindex]:not([tabindex="-1"])';
  return Array.from(container.querySelectorAll(selector)).filter(
    (el) => el.offsetParent !== null || el.getClientRects().length > 0,
  );
}
