import { useState, useMemo } from 'react';

/**
 * useWindowed — bounded rendering for potentially-long lists.
 *
 * Renders only the first `step` rows and exposes a `showMore` to extend the
 * window. This caps the live DOM node count (the real perf risk for unbounded
 * tables like trade history / oracle feeds) without the fragility of
 * pixel-perfect table virtualization, and surfaces an honest "N of M" so the
 * cap is never silent. When the source shrinks (filter/refresh) the window
 * resets to one page.
 *
 * @param {Array} items   the full row list
 * @param {number} step   page size (rows per "show more")
 * @returns {{ rows: Array, total: number, hasMore: boolean, showMore: () => void }}
 */
export function useWindowed(items, step = 100) {
  const list = useMemo(() => (Array.isArray(items) ? items : []), [items]);
  const total = list.length;
  const [limit, setLimit] = useState(step);
  const effectiveLimit = total <= step ? step : Math.min(limit, total);
  const rows = useMemo(
    () => (effectiveLimit >= total ? list : list.slice(0, effectiveLimit)),
    [list, effectiveLimit, total],
  );
  return {
    rows,
    total,
    hasMore: total > rows.length,
    showMore: () => setLimit((l) => l + step),
  };
}
