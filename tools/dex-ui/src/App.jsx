import { useState, lazy, Suspense, useMemo, useCallback } from 'react';
import './index.css';
// Per-surface code-splitting: each tab is a separate chunk loaded on demand, so
// the initial bundle only carries the default (Swap) surface + shell. The other
// nine surfaces (incl. the large Oracle/zUSD/Perps dashboards) load when first
// opened, cutting first-paint JS substantially.
// One importer per tab id, shared by both lazy() and the hover/focus prefetch
// below so warming a chunk on hover resolves the SAME module the click renders.
const SURFACE_IMPORTERS = {
  swap: () => import('./components/SwapInterface'),
  pools: () => import('./components/PoolDashboard'),
  stats: () => import('./components/TokenStats'),
  perps: () => import('./components/perps/PerpTradingView'),
  strategy: () => import('./components/StrategyWorkbench.jsx'),
  zusd: () => import('./components/ZUSDWorkbench.jsx'),
  oracle: () => import('./components/ZenoOracleDashboard.jsx'),
  confidential: () => import('./components/ConfidentialWorkbench.jsx'),
  governance: () => import('./components/PerpsGovernanceSurface.jsx'),
  proofs: () => import('./components/ProofMiningWorkbench.jsx'),
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
const ConfidentialWorkbench = lazy(SURFACE_IMPORTERS.confidential);
const StrategyWorkbench = lazy(SURFACE_IMPORTERS.strategy);
const ZUSDWorkbench = lazy(SURFACE_IMPORTERS.zusd);
const ZenoOracleDashboard = lazy(SURFACE_IMPORTERS.oracle);
const PerpsGovernanceSurface = lazy(SURFACE_IMPORTERS.governance);
const ProofMiningWorkbench = lazy(SURFACE_IMPORTERS.proofs);
import { PerpProvider } from './lib/PerpProvider.jsx';
import { DemoModeProvider } from './lib/DemoModeProvider.jsx';
import { ThemeProvider } from './lib/ThemeContext.jsx';
import ThemeSwitcher from './components/ThemeSwitcher.jsx';
import ErrorBoundary from './components/ErrorBoundary.jsx';
import WalletConnect from './components/WalletConnect';
import TransactionDrawer from './components/TransactionDrawer.jsx';
import { useTransactionCenter } from './lib/TransactionCenterContext.jsx';
import { getRuntimeConfig } from './lib/api.js';
import { useKeyboardShortcuts } from './lib/useKeyboardShortcuts.js';
import CommandPalette from './components/CommandPalette.jsx';

const NAV_TABS = [
  { id: 'swap', label: 'Swap' },
  { id: 'pools', label: 'Pools' },
  { id: 'stats', label: 'ZDEX Stats' },
  { id: 'perps', label: 'Perpetuals' },
  { id: 'strategy', label: 'Strategy' },
  { id: 'zusd', label: 'zUSD' },
  { id: 'oracle', label: 'Oracle' },
  { id: 'confidential', label: 'Confidential' },
  { id: 'proofs', label: 'Proofs' },
  { id: 'governance', label: 'Keys' },
];

const ROUTE_TAB_IDS = new Set([...NAV_TABS.map((tab) => tab.id), 'proofs']);

const ZENODEX_LOGO_ICON = `${import.meta.env.BASE_URL}branding/zenodex/zenodex_icon_256.png`;

function getInitialTab() {
  if (typeof window === 'undefined') {
    return 'swap';
  }
  const requested = new URLSearchParams(window.location.search).get('tab');
  return ROUTE_TAB_IDS.has(requested) ? requested : 'swap';
}

function getInitialWallet() {
  if (typeof window === 'undefined') {
    return null;
  }
  const params = new URLSearchParams(window.location.search);
  if (
    params.get('zenodexUiSmokeSwap') !== '1'
    && params.get('zenodexUiSmokeLiquidity') !== '1'
    && params.get('walletAddress') == null
  ) {
    return null;
  }
  const rawAddress = String(params.get('walletAddress') || '').trim();
  if (!/^(0x)?[0-9a-fA-F]{96}$/.test(rawAddress)) {
    return null;
  }
  const address = rawAddress.toLowerCase().startsWith('0x')
    ? `0x${rawAddress.slice(2).toLowerCase()}`
    : `0x${rawAddress.toLowerCase()}`;
  return {
    address,
    chainId: getRuntimeConfig().chainId || 'zeno-ledger-localtest-v0',
    balance: {
      ZDEX: 1_000_000,
      zUSD: 0,
      tAGRS: 1_000_000,
      TASSET0: 1_000_000,
      TASSET1: 1_000_000,
      TZENO: 1_000_000,
    },
  };
}

function App() {
  const [activeTab, setActiveTab] = useState(getInitialTab);
  const [wallet, setWallet] = useState(getInitialWallet);
  const [cmdkOpen, setCmdkOpen] = useState(false);
  const { upsertTransaction } = useTransactionCenter();
  const uiSurfaceVersion = getRuntimeConfig().uiSurfaceContractVersion || 'ui-unpinned';

  // ── Global keyboard shortcuts ────────────────────────────────────
  // Power-user path: quick tab switching, command palette, theme toggle.
  const switchTab = useCallback((tabId) => {
    setActiveTab(tabId);
    // Update URL for shareable links
    if (typeof window !== 'undefined') {
      const url = new URL(window.location.href);
      url.searchParams.set('tab', tabId);
      window.history.replaceState({}, '', url.toString());
    }
  }, []);

  const toggleTheme = useCallback(() => {
    if (typeof document === 'undefined') return;
    const html = document.documentElement;
    const current = html.getAttribute('data-theme') || 'dark';
    html.setAttribute('data-theme', current === 'dark' ? 'light' : 'dark');
  }, []);

  useKeyboardShortcuts({
    'ctrl+k': (e) => { e.preventDefault(); setCmdkOpen((v) => !v); },
    'alt+1': () => switchTab('swap'),
    'alt+2': () => switchTab('pools'),
    'alt+3': () => switchTab('stats'),
    'alt+4': () => switchTab('perps'),
    'alt+5': () => switchTab('strategy'),
    'alt+6': () => switchTab('zusd'),
    'alt+7': () => switchTab('oracle'),
    'alt+8': () => switchTab('confidential'),
    'alt+9': () => switchTab('proofs'),
    'alt+0': () => switchTab('governance'),
    'alt+t': toggleTheme,
  });

  // Build command palette commands
  const cmdkCommands = useMemo(() => [
    ...NAV_TABS.map((tab, i) => ({
      id: `nav-${tab.id}`,
      label: tab.label,
      hint: i < 9 ? `Alt+${i + 1}` : 'Alt+0',
      icon: '↹',
      group: 'Navigate',
      action: () => switchTab(tab.id),
    })),
    {
      id: 'theme-toggle',
      label: 'Toggle light/dark theme',
      hint: 'Alt+T',
      icon: '◐',
      group: 'Actions',
      action: toggleTheme,
    },
  ], [switchTab, toggleTheme]);

  return (
    <ThemeProvider>
      <DemoModeProvider>
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
              {NAV_TABS.map((tab, i) => (
                <button
                  key={tab.id}
                  className={`nav-link ${activeTab === tab.id ? 'active' : ''}`}
                  onClick={() => switchTab(tab.id)}
                  onMouseEnter={() => prefetchSurface(tab.id)}
                  onFocus={() => prefetchSurface(tab.id)}
                  type="button"
                  aria-current={activeTab === tab.id ? 'page' : undefined}
                  accessKey={i < 9 ? String(i + 1) : '0'}
                  title={i < 9 ? `${tab.label} (Alt+${i + 1})` : `${tab.label} (Alt+0)`}
                >
                  {tab.label}
                </button>
              ))}
            </nav>

            <div className="header-actions">
              <button
                className="cmdk-trigger"
                onClick={() => setCmdkOpen(true)}
                aria-label="Open command palette (Ctrl+K)"
                title="Command palette — Ctrl+K"
                type="button"
              >
                <svg width="14" height="14" viewBox="0 0 16 16" fill="none" aria-hidden="true">
                  <circle cx="7" cy="7" r="5" stroke="currentColor" strokeWidth="1.5" />
                  <path d="M11 11l3 3" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" />
                </svg>
                <kbd>⌘K</kbd>
              </button>
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
          <Suspense fallback={
            <div className="surface-loading" role="status" aria-busy="true" aria-label="Loading surface">
              <span className="surface-loading-spinner" aria-hidden="true" />
              Loading…
            </div>
          }>
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

          {activeTab === 'strategy' && (
            <div className="animate-fade-in">
              <StrategyWorkbench />
            </div>
          )}

          {activeTab === 'zusd' && (
            <div className="animate-fade-in">
              <ZUSDWorkbench wallet={wallet} onConnect={setWallet} />
            </div>
          )}

          {activeTab === 'oracle' && (
            <div className="animate-fade-in">
              <ZenoOracleDashboard wallet={wallet} onConnect={setWallet} />
            </div>
          )}

          {activeTab === 'confidential' && (
            <div className="animate-fade-in">
              <ConfidentialWorkbench />
            </div>
          )}

          {activeTab === 'proofs' && (
            <div className="animate-fade-in">
              <ProofMiningWorkbench />
            </div>
          )}

          {activeTab === 'governance' && (
            <div className="animate-fade-in">
              <PerpsGovernanceSurface />
            </div>
          )}
          </Suspense>
          </ErrorBoundary>
        </main>

        {/* Footer */}
        <footer className="footer">
          <p>
            ZenoDEX: Formally Verified Decentralized Exchange
            <span className="footer-sep">•</span>
            Powered by <a href="https://tau.net" target="_blank" rel="noopener noreferrer">Tau Network</a>
            <span className="footer-sep">•</span>
            <span className="footer-agrs">ZDEX</span> Utility Token
            <span className="footer-version">{uiSurfaceVersion}</span>
          </p>
        </footer>

          <TransactionDrawer />
        </div>

        <CommandPalette
          open={cmdkOpen}
          onOpenChange={setCmdkOpen}
          commands={cmdkCommands}
        />
      </DemoModeProvider>
    </ThemeProvider>
  );
}

export default App;
