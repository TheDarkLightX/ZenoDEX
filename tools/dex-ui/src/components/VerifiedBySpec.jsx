import './VerifiedBySpec.css';

/**
 * VerifiedBySpec - small pill linking a surface to the Tau spec or
 * ESSO model that constrains its consensus-critical path.
 *
 * Props:
 *   spec      string  — short spec name to render, e.g. "cpmm_v1"
 *   kind      'tau' | 'esso' | 'lean' (default 'tau')
 *   href      optional URL to the source artifact (GitHub link)
 *   title     optional tooltip text
 */
function VerifiedBySpec({ spec, kind = 'tau', href, title }) {
    if (!spec) return null;
    const kindLabel = kind === 'esso' ? 'ESSO' : kind === 'lean' ? 'Lean' : 'Tau spec';
    const tooltip = title
        || `Consensus-critical path is constrained by ${kindLabel} ${spec}. Runtime admission and ledger acceptance remain authoritative.`;
    const body = (
        <>
            <span className="verified-by-spec-check" aria-hidden="true">✓</span>
            <span className="verified-by-spec-label">
                Spec-bound <span className="verified-by-spec-name">{spec}</span>
            </span>
        </>
    );
    if (href) {
        return (
            <a
                className="verified-by-spec"
                href={href}
                target="_blank"
                rel="noopener noreferrer"
                title={tooltip}
            >
                {body}
            </a>
        );
    }
    return (
        <span className="verified-by-spec verified-by-spec-static" title={tooltip}>
            {body}
        </span>
    );
}

export default VerifiedBySpec;
