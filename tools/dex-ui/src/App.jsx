import { useState, lazy, Suspense } from 'react';
import './index.css';
// Per-surface code-splitting: each tab is a separate chunk loaded on demand, so
// the initial bundle only carries the default (Swap) surface + shell. The other
// five surfaces (including the large Oracle/zUSD/Perps dashboards) load when first
// opened, cutting first-paint JS substantially.
// One importer per tab id, shared by both lazy() and the hover/focus prefetch
// below so warming a chunk on hover resolves the SAME module the click renders.
const SURFACE_IMPORTERS = {
  swap: () => import('./components/SwapInterface'),
  pools: () => import('./components/PoolDashboard'),
  stats: () => import('./components/TokenStats'),
  perps: () => import('./components/perps/PerpTradingView'),
  zusd: () => import('./components/ZUSDWorkbench.jsx'),
  oracle: () => import('./components/ZenoOracleDashboard.jsx'),
};
// Prefetch a surface chunk (idempotent — dynamic import() caches the request).
function prefetchSurface(id) {
  const load = SURFACE_IMPORTERS[id];
  if (load) load().catch(() => { /* hover prefetch is best-effort */ });
}
const SwapInterface = lazy(SURFACE_IMPORTERS.swap);
const PoolDashboard = lazy(SURFACE_IMPORTERS.pools);
const TokenStats = lazy(SURFACE_IMPORTERS.stats);
const PerpTradingView = lazy(SURFACE_IMPORTERS.perps);
const ZUSDWorkbench = lazy(SURFACE_IMPORTERS.zusd);
const ZenoOracleDashboard = lazy(SURFACE_IMPORTERS.oracle);
import { PerpProvider } from './lib/PerpProvider.jsx';
import { ThemeProvider } from './lib/ThemeContext.jsx';
import ThemeSwitcher from './components/ThemeSwitcher.jsx';
import ErrorBoundary from './components/ErrorBoundary.jsx';
import WalletConnect from './components/WalletConnect';
import TransactionDrawer from './components/TransactionDrawer.jsx';
import { useTransactionCenter } from './lib/TransactionCenterContext.jsx';
import { getRuntimeConfig } from './lib/api.js';

const NAV_TABS = [
  { id: 'swap', label: 'Swap' },
  { id: 'pools', label: 'Pools' },
  { id: 'stats', label: 'ZDEX Stats' },
  { id: 'perps', label: 'Perpetuals' },
  { id: 'zusd', label: 'zUSD' },
  { id: 'oracle', label: 'Oracle' },
];

const ROUTE_TAB_IDS = new Set(NAV_TABS.map((tab) => tab.id));

const ZENODEX_LOGO_ICON = `${import.meta.env.BASE_URL}branding/zenodex/zenodex_icon_256.png`;

function getInitialTab() {
  if (typeof window === 'undefined') {
    return 'swap';
  }
  const requested = new URLSearchParams(window.location.search).get('tab');
  return ROUTE_TAB_IDS.has(requested) ? requested : 'swap';
}

function App() {
  const [activeTab, setActiveTab] = useState(getInitialTab);
  const [wallet, setWallet] = useState(null);
  const { upsertTransaction } = useTransactionCenter();
  const uiSurfaceVersion = getRuntimeConfig().uiSurfaceContractVersion || 'ui-unpinned';

  return (
    <ThemeProvider>
      <div className={`app-container ${activeTab === 'oracle' ? 'app-container-oracle' : ''}`}>
          {/* Header */}
          <header className="header">
            <div className="logo">
              <img
                className="logo-icon"
                src={ZENODEX_LOGO_ICON}
                alt="ZenoDEX"
              />
              <span className="logo-text">
                Zeno<span className="logo-highlight">DEX</span>
              </span>
            </div>

            <nav className="nav" aria-label="Product windows">
              {NAV_TABS.map((tab) => (
                <button
                  key={tab.id}
                  className={`nav-link ${activeTab === tab.id ? 'active' : ''}`}
                  onClick={() => setActiveTab(tab.id)}
                  onMouseEnter={() => prefetchSurface(tab.id)}
                  onFocus={() => prefetchSurface(tab.id)}
                  type="button"
                >
                  {tab.label}
                </button>
              ))}
            </nav>

            <div className="header-actions">
              <ThemeSwitcher />
              <WalletConnect wallet={wallet} onConnect={setWallet} />
            </div>
          </header>

        {/* Main Content */}
        <main className={`main ${activeTab === 'oracle' ? 'main-oracle' : ''}`}>
          {/* Per-route fault isolation: a crash in one surface keeps the
              header/nav/footer alive and lets the user switch tabs. Keying by
              activeTab resets the boundary when the surface changes. */}
          <ErrorBoundary key={activeTab}>
          <Suspense fallback={<div className="surface-loading" role="status">Loading…</div>}>
          {activeTab === 'swap' && (
            <div className="swap-container animate-fade-in">
              <SwapInterface wallet={wallet} />
            </div>
          )}

          {activeTab === 'pools' && (
            <div className="animate-fade-in">
              <PoolDashboard wallet={wallet} />
            </div>
          )}

          {activeTab === 'stats' && (
            <div className="animate-fade-in">
              <TokenStats />
            </div>
          )}

          {activeTab === 'perps' && (
            <div className="animate-fade-in">
              <PerpProvider wallet={wallet} onTransaction={upsertTransaction}>
                <PerpTradingView wallet={wallet} />
              </PerpProvider>
            </div>
          )}

          {activeTab === 'zusd' && (
            <div className="animate-fade-in">
              <ZUSDWorkbench />
            </div>
          )}

          {activeTab === 'oracle' && (
            <div className="animate-fade-in">
              <ZenoOracleDashboard wallet={wallet} onConnect={setWallet} />
            </div>
          )}

          </Suspense>
          </ErrorBoundary>
        </main>

        {/* Footer */}
        <footer className="footer">
          <p>
            ZenoDEX: Deterministic Decentralized Exchange
            <span className="footer-sep">•</span>
            Powered by <a href="https://tau.net" target="_blank" rel="noopener noreferrer">Tau Network</a>
            <span className="footer-sep">•</span>
            <span className="footer-agrs">ZDEX</span> Utility Token
            <span className="footer-version">{uiSurfaceVersion}</span>
          </p>
        </footer>

          <TransactionDrawer />
      </div>
    </ThemeProvider>
  );
}

export default App;
