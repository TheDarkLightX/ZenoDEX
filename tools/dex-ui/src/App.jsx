import { useState } from 'react';
import './index.css';
import SwapInterface from './components/SwapInterface';
import PoolDashboard from './components/PoolDashboard';
import TokenStats from './components/TokenStats';
import PerpTradingView from './components/perps/PerpTradingView';
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
];

function App() {
  const [activeTab, setActiveTab] = useState('swap');
  const [wallet, setWallet] = useState(null);
  const { upsertTransaction } = useTransactionCenter();

  return (
    <div className="app-container">
      {/* Header */}
      <header className="header">
        <div className="logo">
          <div className="logo-icon">
            <span className="logo-z">Z</span>
          </div>
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
      <main className="main">
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
            <DemoModeProvider>
              <PerpProvider wallet={wallet} onTransaction={upsertTransaction}>
                <PerpTradingView wallet={wallet} />
              </PerpProvider>
            </DemoModeProvider>
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
        </p>
      </footer>

      <TransactionDrawer />
    </div>
  );
}

export default App;
