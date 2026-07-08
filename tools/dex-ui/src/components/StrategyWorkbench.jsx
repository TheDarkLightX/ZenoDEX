// Copyright DarkLightX/Dana Edwards
// StrategyWorkbench — v3 layout with task tabs, system status, progressive disclosure

import { useState } from 'react';
import './strategy/StrategySection.css';
import StrategyStatusBar from './strategy/StrategyStatusBar.jsx';
import StrategyTabs from './strategy/StrategyTabs.jsx';
import { useStrategyTab } from './strategy/useStrategyTab.js';
import StrategiesTab from './strategy/StrategiesTab.jsx';
import SafetyTab from './strategy/SafetyTab.jsx';
import DeveloperTab from './strategy/DeveloperTab.jsx';
import { useDemoMode } from '../lib/DemoModeContext.jsx';
import { DEMO_STRATEGIES } from '../lib/strategyData.js';

function StrategyWorkbench() {
  const [activeTab, setActiveTab] = useStrategyTab();
  const [systemState, setSystemState] = useState('online');
  const [signedPayload] = useState('');
  const { demoMode } = useDemoMode();
  const activeCount = demoMode
    ? DEMO_STRATEGIES.filter((s) => s.status === 'active').length
    : 0;

  function handleSystemRefresh() {
    setSystemState('online');
  }

  function handlePauseAll() {
    // No-op until real strategies are tracked from API
  }

  function handleResumeAll() {
    // No-op until real strategies are tracked from API
  }

  return (
    <section className="strategy-section strategy-workbench" id="strategy-workbench">
      <div className="strategy-header">
        <h1>Strategy</h1>
        <p className="strategy-header-subtitle">
          Create and monitor automated trading strategies with safety limits.
        </p>
      </div>

      <StrategyStatusBar
        onRefresh={handleSystemRefresh}
        onPauseAll={handlePauseAll}
        systemState={systemState}
        activeCount={activeCount}
      />

      <StrategyTabs activeTab={activeTab} onTabChange={setActiveTab} />

      {activeTab === 'strategies' && (
        <StrategiesTab systemStatus={systemState} />
      )}
      {activeTab === 'safety' && (
        <SafetyTab
          systemStatus={systemState}
          signedPayload={signedPayload}
          onPauseAll={handlePauseAll}
          onResumeAll={handleResumeAll}
        />
      )}
      {activeTab === 'developer' && (
        <DeveloperTab />
      )}
    </section>
  );
}

export default StrategyWorkbench;
