import { useState } from 'react';
import './index.css';
import SwapInterface from './components/SwapInterface';
import PoolDashboard from './components/PoolDashboard';
import TokenStats from './components/TokenStats';
import PerpTradingView from './components/perps/PerpTradingView';
import ConfidentialWorkbench from './components/ConfidentialWorkbench.jsx';
import StrategyWorkbench from './components/StrategyWorkbench.jsx';
import ZUSDWorkbench from './components/ZUSDWorkbench.jsx';
import ZenoOracleDashboard from './components/ZenoOracleDashboard.jsx';
import { PerpProvider } from './lib/PerpProvider.jsx';
import { DemoModeProvider } from './lib/DemoModeProvider.jsx';
import WalletConnect from './components/WalletConnect';
import TransactionDrawer from './components/TransactionDrawer.jsx';
import { useTransactionCenter } from './lib/TransactionCenterContext.jsx';

const APP_TABS = [
  { id: 'swap', label: 'Swap' },
  { id: 'pools', label: 'Pools' },
  { id: 'stats', label: 'ZDEX Stats' },
  { id: 'perps', label: 'Perpetuals' },
  { id: 'strategy', label: 'Strategy' },
  { id: 'zusd', label: 'zUSD' },
  { id: 'oracle', label: 'Oracle' },
  { id: 'confidential', label: 'Confidential' },
];

const ZENODEX_LOGO_ICON = `${import.meta.env.BASE_URL}branding/zenodex/zenodex_icon_256.png`;

function getInitialTab() {
  if (typeof window === 'undefined') {
    return 'swap';
  }
  const requested = new URLSearchParams(window.location.search).get('tab');
  return APP_TABS.some((tab) => tab.id === requested) ? requested : 'swap';
}

function getInitialWallet() {
  if (typeof window === 'undefined') {
    return null;
  }
  const params = new URLSearchParams(window.location.search);
  if (params.get('zenodexUiSmokeSwap') !== '1') {
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
    chainId: 'tau-alpha',
    balance: {
      AGRS: 1_000_000,
      ZDEX: 1_000_000,
      USD: 1_000_000,
      TASSET0: 1_000_000,
      TASSET1: 1_000_000,
      TZENO: 1_000_000,
    },
  };
}

function App() {
  const [activeTab, setActiveTab] = useState(getInitialTab);
  const [wallet, setWallet] = useState(getInitialWallet);
  const { upsertTransaction } = useTransactionCenter();

  return (
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
            {APP_TABS.map((tab) => (
              <button
                key={tab.id}
                className={`nav-link ${activeTab === tab.id ? 'active' : ''}`}
                onClick={() => setActiveTab(tab.id)}
                type="button"
              >
                {tab.label}
              </button>
            ))}
          </nav>

          <WalletConnect wallet={wallet} onConnect={setWallet} />
        </header>

        {/* Main Content */}
        <main className={`main ${activeTab === 'oracle' ? 'main-oracle' : ''}`}>
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
              <ZUSDWorkbench />
            </div>
          )}

          {activeTab === 'oracle' && (
            <div className="animate-fade-in">
              <ZenoOracleDashboard />
            </div>
          )}

          {activeTab === 'confidential' && (
            <div className="animate-fade-in">
              <ConfidentialWorkbench />
            </div>
          )}
        </main>

        {/* Footer */}
        <footer className="footer">
          <p>
            ZenoDEX: Formally Verified Decentralized Exchange
            <span className="footer-sep">•</span>
            Powered by <a href="https://tau.net" target="_blank" rel="noopener noreferrer">Tau Network</a>
            <span className="footer-sep">•</span>
            <span className="footer-agrs">AGRS</span> Native Token
            <span className="footer-version">v1.0.0-alpha</span>
          </p>
        </footer>

        <TransactionDrawer />
      </div>
    </DemoModeProvider>
  );
}

export default App;
