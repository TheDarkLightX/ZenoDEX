// Copyright (c) DarkLightX/Dana Edwards. All rights reserved.

import { formatPercent } from '../../lib/cpmm';
import { getSlippageOptions } from '../../lib/validation';
import { sliderValueForProfile } from '../../lib/routeProfiles';
import { Tooltip } from './SwapTooltip';
import { InfoIcon } from './SwapIcons';

export function SwapSettings({
    suggestedSlippage,
    slippage,
    setSlippage,
    slippageAdviceNotice,
    pokayokeEnabled,
    setPokayokeEnabled,
    advancedMode,
    setAdvancedMode,
    autoProfile,
    setAutoProfile,
    profileSlider,
    setProfileSlider,
    effectiveProfileConfig,
    routeProfiles,
}) {
    return (
        <div className="settings-panel animate-slide-up">
            <div className="settings-row">
                <span className="label">
                    <Tooltip text="Maximum price movement you're willing to accept">
                        <span className="label-with-icon">Slippage Tolerance <InfoIcon /></span>
                    </Tooltip>
                </span>
                {suggestedSlippage !== slippage && (
                    <button
                        className="suggested-btn"
                        onClick={() => setSlippage(suggestedSlippage)}
                    >
                        Use calculated ({formatPercent(suggestedSlippage)})
                    </button>
                )}
            </div>
            <div className="slippage-options">
                {getSlippageOptions().map(opt => (
                    <button
                        key={opt.value}
                        className={`slippage-btn ${slippage === opt.value ? 'active' : ''}`}
                        onClick={() => setSlippage(opt.value)}
                    >
                        {opt.label}
                    </button>
                ))}
            </div>

            {slippageAdviceNotice && (
                <div className={slippageAdviceNotice.kind === 'warning' ? 'swap-warning' : 'swap-notice'}>
                    {slippageAdviceNotice.text}
                </div>
            )}

            <div className="settings-row">
                <span className="label">
                    <Tooltip text="Enable extra confirmation steps for risky swaps (protects against unfavorable execution)">
                        <span className="label-with-icon">Extra Safety Checks (Experimental) <InfoIcon /></span>
                    </Tooltip>
                </span>
                <button
                    className={`automation-toggle ${pokayokeEnabled ? 'enabled' : ''}`}
                    onClick={() => setPokayokeEnabled((prev) => !prev)}
                    type="button"
                >
                    {pokayokeEnabled ? 'Enabled' : 'Disabled'}
                </button>
            </div>

            <div className="settings-row">
                <span className="label">
                    <Tooltip text="Enable advanced swap path optimization and quote verification">
                        <span className="label-with-icon">Advanced Mode <InfoIcon /></span>
                    </Tooltip>
                </span>
                <button
                    className={`automation-toggle ${advancedMode ? 'enabled' : ''}`}
                    onClick={() => setAdvancedMode((prev) => !prev)}
                    type="button"
                >
                    {advancedMode ? 'Enabled' : 'Disabled'}
                </button>
            </div>

            {advancedMode && (
                <>
                    <div className="settings-divider" />
                    <div className="settings-row">
                        <span className="label">
                            <Tooltip text="Balance between speed and price quality">
                                <span className="label-with-icon">Swap Path Preference <InfoIcon /></span>
                            </Tooltip>
                        </span>
                        <button
                            className={`automation-toggle ${autoProfile ? 'enabled' : ''}`}
                            onClick={() => setAutoProfile((prev) => !prev)}
                            type="button"
                        >
                            {autoProfile ? 'Auto On' : 'Auto Off'}
                        </button>
                    </div>
                    <div className="profile-slider-wrap">
                        <input
                            type="range"
                            min="0"
                            max="100"
                            value={autoProfile ? sliderValueForProfile(effectiveProfileConfig.id) : profileSlider}
                            onChange={(e) => setProfileSlider(Number(e.target.value))}
                            disabled={autoProfile}
                            className="profile-slider"
                        />
                        <div className="profile-labels">
                            {routeProfiles.map((profile) => (
                                <span
                                    key={profile.id}
                                    className={`profile-chip ${effectiveProfileConfig.id === profile.id ? 'active' : ''}`}
                                >
                                    {profile.label}
                                </span>
                            ))}
                        </div>
                    </div>
                    <div className="profile-description">
                        <strong>{effectiveProfileConfig.label}</strong>: {effectiveProfileConfig.description}
                    </div>
                </>
            )}
        </div>
    );
}
