// Copyright DarkLightX/Dana Edwards
// Trusted Devices — simplified table view. Fingerprints, key IDs, copy behind [Details].

import { useState } from 'react';

function shortAlgo(a) {
  return String(a || '').replace(/-release.*$/, '').replace(/^bls12-381-/, 'BLS ');
}

function DeviceDetails({ signer, keyRef, onClose }) {
  const [copied, setCopied] = useState(false);
  const keyId = signer.key_id || 'unknown';
  const pubkey = keyRef?.public_key || '';

  const handleCopy = async () => {
    try {
      await navigator.clipboard.writeText(pubkey);
      setCopied(true);
      setTimeout(() => setCopied(false), 1500);
    } catch {
      // Clipboard may be unavailable
    }
  };

  return (
    <div className="device-details-panel" role="dialog" aria-label={`Details for ${signer.signer_id || keyId}`}>
      <div className="device-details-header">
        <h4>{signer.signer_id || keyId}</h4>
        <button className="btn btn-ghost btn-xs" type="button" onClick={onClose} aria-label="Close details">✕</button>
      </div>
      <div className="device-details-grid">
        <div className="device-details-row">
          <span>Device ID</span>
          <span className="gov-mono">{keyId}</span>
        </div>
        <div className="device-details-row">
          <span>Key type</span>
          <span>{shortAlgo(keyRef?.algorithm)}</span>
        </div>
        <div className="device-details-row">
          <span>Status</span>
          <span>{keyRef?.status || 'unknown'}</span>
        </div>
        <div className="device-details-row">
          <span>Signing power</span>
          <span>{signer.weight ?? 1}</span>
        </div>
        <div className="device-details-row">
          <span>Device key</span>
          <div className="device-details-pubkey">
            <span className="gov-mono">{pubkey.slice(0, 20)}…{pubkey.slice(-12)}</span>
            <button className="btn btn-ghost btn-xs" type="button" onClick={handleCopy} aria-label="Copy device key">
              {copied ? '✓ Copied' : '⧉ Copy'}
            </button>
          </div>
        </div>
      </div>
    </div>
  );
}

function DeviceRow({ signer, keyRef, onDetails }) {
  const keyId = signer.key_id || 'unknown';
  const isActive = keyRef?.status === 'active';

  return (
    <div className="device-row" role="row">
      <div className="device-row-name">{signer.signer_id || keyId}</div>
      <div className="device-row-status">
        <span className={`device-signing-dot ${isActive ? 'dot-active' : 'dot-inactive'}`} aria-hidden="true"></span>
        {isActive ? 'Can sign' : 'Cannot sign'}
      </div>
      <div className="device-row-lastused">—</div>
      <button className="btn btn-ghost btn-sm device-row-details" type="button" onClick={() => onDetails(signer)}>
        Details
      </button>
    </div>
  );
}

export default function TrustedDevices({ activeSigners, keyRefs, onAddDevice }) {
  const [expandedDevice, setExpandedDevice] = useState(null);
  const keyRefById = new Map((keyRefs || []).map((k) => [k.key_id, k]));
  const signers = activeSigners || [];

  return (
    <div className="trusted-devices-panel" role="region" aria-label="Trusted devices">
      <div className="trusted-devices-header">
        <h3>Trusted Devices</h3>
        <button className="btn btn-secondary btn-sm" type="button" onClick={onAddDevice}>Add trusted device</button>
      </div>
      <div className="trusted-devices-table" role="table">
        <div className="device-table-header" role="row">
          <span>Device</span>
          <span>Can approve</span>
          <span>Last used</span>
          <span>Action</span>
        </div>
        {signers.map((s) => (
          <DeviceRow key={s.signer_id || s.key_id} signer={s} keyRef={keyRefById.get(s.key_id)} onDetails={setExpandedDevice} />
        ))}
        {signers.length === 0 && <div className="device-table-empty">No trusted devices loaded</div>}
      </div>
      {expandedDevice && (
        <DeviceDetails
          signer={expandedDevice}
          keyRef={keyRefById.get(expandedDevice.key_id)}
          onClose={() => setExpandedDevice(null)}
        />
      )}
    </div>
  );
}
