import { useId } from 'react';
import './InfoTip.css';

export default function InfoTip({ label, children, align = 'top' }) {
  const id = useId();
  return (
    <span className={`infotip infotip-${align}`}>
      <button
        type="button"
        className="infotip-trigger"
        aria-describedby={id}
        aria-label={typeof children === 'string' ? children : 'More info'}
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
