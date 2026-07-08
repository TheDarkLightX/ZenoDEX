import { useId, useState, useCallback, useRef, useEffect } from 'react';
import './InfoTip.css';

export default function InfoTip({ label, children, align = 'top' }) {
  const id = useId();
  const [open, setOpen] = useState(false);
  const tipRef = useRef(null);

  // Close on outside click when toggled open
  useEffect(() => {
    if (!open) return;
    const handler = (e) => {
      if (tipRef.current && !tipRef.current.contains(e.target)) {
        setOpen(false);
      }
    };
    document.addEventListener('mousedown', handler);
    return () => document.removeEventListener('mousedown', handler);
  }, [open]);

  const handleKeyDown = useCallback((e) => {
    if (e.key === 'Escape') setOpen(false);
  }, []);

  return (
    <span
      className={`infotip infotip-${align} ${open ? 'infotip-open' : ''}`}
      ref={tipRef}
      onKeyDown={handleKeyDown}
    >
      <button
        type="button"
        className="infotip-trigger"
        aria-describedby={id}
        aria-label={typeof children === 'string' ? children : 'More info'}
        aria-expanded={open}
        onClick={() => setOpen((v) => !v)}
      >
        ?
      </button>
      <span className="infotip-bubble" role="tooltip" id={id}>
        {label ? <strong className="infotip-label">{label}</strong> : null}
        <span className="infotip-body">{children}</span>
      </span>
    </span>
  );
}
