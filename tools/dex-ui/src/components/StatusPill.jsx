import './StatusPill.css';

/**
 * Status pill — outlined with currentColor + dot. Used across Confidential,
 * Oracle, Perps. One semantic tone per role:
 *   - ok     → confirmed / healthy / accepted
 *   - warn   → attention / partial / configuration incomplete
 *   - err    → failed / rejected / unavailable
 *   - idle   → muted, no opinion (e.g. demo mode, not yet attempted)
 */
function StatusPill({ tone = 'idle', label, children }) {
  const text = label ?? children;
  return (
    <span
      className={`status-pill status-pill-${tone}`}
      role="status"
      aria-live="polite"
      aria-label={typeof text === 'string' ? text : undefined}
    >
      <span className="status-pill-dot" aria-hidden="true" />
      {text}
    </span>
  );
}

export default StatusPill;
