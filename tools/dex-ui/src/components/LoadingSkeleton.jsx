import './LoadingSkeleton.css';

/**
 * LoadingSkeleton - Animated placeholder for loading states
 * Provides visual feedback while data is being fetched
 */

export function SkeletonLine({ width = '100%', height = '1rem' }) {
    return (
        <div
            className="skeleton-line"
            style={{ width, height }}
            aria-hidden="true"
        />
    );
}

export function SkeletonCard({ lines = 3 }) {
    return (
        <div className="skeleton-card panel" role="status" aria-label="Loading" aria-busy="true">
            <SkeletonLine width="60%" height="1.25rem" />
            <div className="skeleton-spacer" />
            {Array.from({ length: lines }).map((_, i) => (
                <SkeletonLine key={i} width={`${80 - i * 10}%`} />
            ))}
        </div>
    );
}

export function SkeletonTable({ rows = 3, cols = 4 }) {
    return (
        <div className="skeleton-table panel" role="status" aria-label="Loading table" aria-busy="true">
            <div className="skeleton-header">
                {Array.from({ length: cols }).map((_, i) => (
                    <SkeletonLine key={i} width="80%" height="0.75rem" />
                ))}
            </div>
            {Array.from({ length: rows }).map((_, rowIndex) => (
                <div key={rowIndex} className="skeleton-row">
                    {Array.from({ length: cols }).map((_, colIndex) => (
                        <SkeletonLine key={colIndex} width="70%" />
                    ))}
                </div>
            ))}
        </div>
    );
}

export function SkeletonSwap() {
    return (
        <div className="skeleton-swap panel" role="status" aria-label="Loading swap interface" aria-busy="true">
            <SkeletonLine width="40%" height="1.5rem" />
            <div className="skeleton-spacer-lg" />
            <div className="skeleton-input-box">
                <SkeletonLine width="30%" height="0.75rem" />
                <SkeletonLine width="60%" height="2rem" />
            </div>
            <div className="skeleton-swap-arrow">
                <SkeletonLine width="2rem" height="2rem" />
            </div>
            <div className="skeleton-input-box">
                <SkeletonLine width="30%" height="0.75rem" />
                <SkeletonLine width="60%" height="2rem" />
            </div>
            <div className="skeleton-spacer-lg" />
            <SkeletonLine width="100%" height="3rem" />
        </div>
    );
}

export function SkeletonStats() {
    return (
        <div className="skeleton-stats" role="status" aria-label="Loading statistics" aria-busy="true">
            <SkeletonLine width="50%" height="1.75rem" />
            <div className="skeleton-spacer-lg" />
            <div className="skeleton-grid">
                <SkeletonCard lines={2} />
                <SkeletonCard lines={2} />
                <SkeletonCard lines={2} />
                <SkeletonCard lines={2} />
            </div>
        </div>
    );
}

export default {
    SkeletonLine,
    SkeletonCard,
    SkeletonTable,
    SkeletonSwap,
    SkeletonStats,
};
