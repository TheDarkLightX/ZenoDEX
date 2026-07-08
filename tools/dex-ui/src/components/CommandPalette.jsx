import { useState, useEffect, useRef, useMemo, useCallback } from 'react';
import { useKeyboardShortcuts } from '../lib/useKeyboardShortcuts.js';
import './CommandPalette.css';

/**
 * CommandPalette — a Cmd/Ctrl+K power-user command centre.
 *
 * Shows a searchable list of actions (navigate to tabs, toggle theme,
 * connect wallet, etc.). Fuzzy-matched by label. Keyboard-first:
 * ArrowUp/Down to navigate, Enter to execute, Escape to dismiss.
 *
 * @param {boolean} open
 * @param {(open: boolean) => void} onOpenChange
 * @param {Array<{id: string, label: string, hint?: string, icon?: string, action: () => void, group?: string}>} commands
 */
export default function CommandPalette({ open, onOpenChange, commands }) {
  const [query, setQuery] = useState('');
  const [selectedIdx, setSelectedIdx] = useState(0);
  const inputRef = useRef(null);
  const listRef = useRef(null);

  const filtered = useMemo(() => {
    if (!query.trim()) return commands;
    const q = query.toLowerCase();
    return commands.filter((cmd) => {
      const text = (cmd.label + ' ' + (cmd.hint || '') + ' ' + (cmd.group || '')).toLowerCase();
      // Simple subsequence fuzzy match
      let qi = 0;
      for (let i = 0; i < text.length && qi < q.length; i++) {
        if (text[i] === q[qi]) qi++;
      }
      return qi === q.length;
    });
  }, [query, commands]);

  useEffect(() => {
    setSelectedIdx(0);
  }, [query]);

  useEffect(() => {
    if (open) {
      setQuery('');
      setSelectedIdx(0);
      // Focus input after render
      requestAnimationFrame(() => inputRef.current?.focus());
    }
  }, [open]);

  // Scroll selected item into view
  useEffect(() => {
    if (!open || !listRef.current) return;
    const item = listRef.current.children[selectedIdx];
    if (item) item.scrollIntoView({ block: 'nearest' });
  }, [selectedIdx, open]);

  const execute = useCallback(
    (cmd) => {
      if (!cmd) return;
      cmd.action();
      onOpenChange(false);
    },
    [onOpenChange],
  );

  useKeyboardShortcuts(
    {
      escape: () => onOpenChange(false),
      arrowdown: (e) => {
        e.stopPropagation();
        setSelectedIdx((i) => Math.min(i + 1, filtered.length - 1));
      },
      arrowup: (e) => {
        e.stopPropagation();
        setSelectedIdx((i) => Math.max(i - 1, 0));
      },
      enter: (e) => {
        e.stopPropagation();
        execute(filtered[selectedIdx]);
      },
    },
    { enabled: open },
  );

  // Group commands for display
  const grouped = useMemo(() => {
    const groups = new Map();
    for (const cmd of filtered) {
      const g = cmd.group || 'Actions';
      if (!groups.has(g)) groups.set(g, []);
      groups.get(g).push(cmd);
    }
    return Array.from(groups.entries());
  }, [filtered]);

  if (!open) return null;

  // Flatten for index tracking
  let flatIdx = -1;

  return (
    <div className="cmdk-overlay" onClick={() => onOpenChange(false)} role="presentation">
      <div
        className="cmdk-panel"
        onClick={(e) => e.stopPropagation()}
        role="dialog"
        aria-modal="true"
        aria-label="Command palette"
      >
        <div className="cmdk-input-row">
          <svg className="cmdk-search-icon" width="16" height="16" viewBox="0 0 16 16" fill="none" aria-hidden="true">
            <circle cx="7" cy="7" r="5" stroke="currentColor" strokeWidth="1.5" />
            <path d="M11 11l3 3" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" />
          </svg>
          <input
            ref={inputRef}
            className="cmdk-input"
            type="text"
            placeholder="Search commands…"
            value={query}
            onChange={(e) => setQuery(e.target.value)}
            aria-label="Search commands"
            aria-controls="cmdk-list"
            aria-activedescendant={filtered[selectedIdx] ? `cmdk-item-${filtered[selectedIdx].id}` : undefined}
          />
          <kbd className="cmdk-esc">ESC</kbd>
        </div>

        {filtered.length === 0 ? (
          <div className="cmdk-empty">No commands found</div>
        ) : (
          <div className="cmdk-list" id="cmdk-list" ref={listRef} role="listbox">
            {grouped.map(([group, items]) => (
              <div key={group} className="cmdk-group">
                <div className="cmdk-group-label">{group}</div>
                {items.map((cmd) => {
                  flatIdx++;
                  const idx = flatIdx;
                  return (
                    <button
                      key={cmd.id}
                      id={`cmdk-item-${cmd.id}`}
                      className={`cmdk-item ${idx === selectedIdx ? 'cmdk-item-active' : ''}`}
                      onClick={() => execute(cmd)}
                      onMouseEnter={() => setSelectedIdx(idx)}
                      role="option"
                      aria-selected={idx === selectedIdx}
                      type="button"
                    >
                      <span className="cmdk-item-icon" aria-hidden="true">
                        {cmd.icon || '›'}
                      </span>
                      <span className="cmdk-item-label">{cmd.label}</span>
                      {cmd.hint && <kbd className="cmdk-item-hint">{cmd.hint}</kbd>}
                    </button>
                  );
                })}
              </div>
            ))}
          </div>
        )}

        <div className="cmdk-footer">
          <span><kbd>↑</kbd><kbd>↓</kbd> navigate</span>
          <span><kbd>↵</kbd> select</span>
          <span><kbd>esc</kbd> close</span>
        </div>
      </div>
    </div>
  );
}
