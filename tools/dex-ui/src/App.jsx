import { useState } from 'react';
import './index.css';
import SwapInterface from './components/SwapInterface';
import PoolDashboard from './components/PoolDashboard';
import TokenStats from './components/TokenStats';
import WalletConnect from './components/WalletConnect';

function App() {
  const [activeTab, setActiveTab] = useState('swap');
  const [wallet, setWallet] = useState(null);

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

        <nav className="nav">
          <button
            className={`nav-link ${activeTab === 'swap' ? 'active' : ''}`}
            onClick={() => setActiveTab('swap')}
          >
            Swap
          </button>
          <button
            className={`nav-link ${activeTab === 'pools' ? 'active' : ''}`}
            onClick={() => setActiveTab('pools')}
          >
            Pools
          </button>
          <button
            className={`nav-link ${activeTab === 'stats' ? 'active' : ''}`}
            onClick={() => setActiveTab('stats')}
          >
            ZDEX Stats
          </button>
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
    </div>
  );
}

export default App;
