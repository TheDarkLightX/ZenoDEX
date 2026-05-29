import { useState } from 'react';
import './CopyHash.css';

/**
 * CopyHash — click-to-copy chip for long identifiers. Truncates the
 * middle (8 head … 6 tail) and reveals "copied" feedback for ~1.2s.
 * Used wherever the UI renders a hash, address, or any opaque long
 * string. Renders an italic placeholder when value is empty/null.
 */
function CopyHash({ value, label = 'value', placeholder = 'not yet produced', head = 8, tail = 6 }) {
  const [copied, setCopied] = useState(false);

  if (!value) {
    return <span className="copy-hash-empty">{placeholder}</span>;
  }

  const truncated = trunc(value, head, tail);

  async function handleClick() {
    try {
      await navigator.clipboard.writeText(String(value));
      setCopied(true);
      window.setTimeout(() => setCopied(false), 1200);
    } catch {
      // Clipboard may be unavailable (insecure context, sandbox). Fail
      // silently — the user can still triple-click + copy the visible
      // text from the title attribute.
    }
  }

  return (
    <button
      type="button"
      className="copy-hash"
      onClick={handleClick}
      title={`Copy ${label}`}
    >
      <span className="copy-hash-mono">{truncated}</span>
      <span className="copy-hash-action">{copied ? 'copied' : 'copy'}</span>
    </button>
  );
}

function trunc(value, head, tail) {
  const s = String(value);
  if (s.length <= head + tail + 1) return s;
  return `${s.slice(0, head)}…${s.slice(-tail)}`;
}

export default CopyHash;
