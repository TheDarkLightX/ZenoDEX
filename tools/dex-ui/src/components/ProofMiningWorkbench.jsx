// Copyright DarkLightX/Dana Edwards
// ProofMiningWorkbench — v3 layout with task tabs, system status, progressive disclosure

import { useState } from 'react';
import './proofs/ProofsSection.css';
import ProofsStatusBar from './proofs/ProofsStatusBar.jsx';
import ProofsTabs from './proofs/ProofsTabs.jsx';
import { useProofsTab } from './proofs/useProofsTab.js';
import ClaimRewardTab from './proofs/ClaimRewardTab.jsx';
import VerifyCheckpointTab from './proofs/VerifyCheckpointTab.jsx';
import ApiReferenceTab from './proofs/ApiReferenceTab.jsx';

function ProofMiningWorkbench() {
  const [activeTab, setActiveTab] = useProofsTab();
  const [systemState, setSystemState] = useState('online');

  function handleSystemRefresh() {
    setSystemState('online');
  }

  return (
    <section className="proofs-section proof-mining-workbench" id="proof-mining-workbench">
      <div className="proofs-header">
        <h1>Proofs</h1>
        <p className="proofs-header-subtitle">
          Claim rewards, verify checkpoints, or view API docs.
        </p>
      </div>

      <ProofsStatusBar onRefresh={handleSystemRefresh} />

      <ProofsTabs activeTab={activeTab} onTabChange={setActiveTab} />

      {activeTab === 'claim' && (
        <ClaimRewardTab systemStatus={systemState} />
      )}
      {activeTab === 'checkpoint' && (
        <VerifyCheckpointTab systemStatus={systemState} />
      )}
      {activeTab === 'api' && (
        <ApiReferenceTab />
      )}
    </section>
  );
}

export default ProofMiningWorkbench;
