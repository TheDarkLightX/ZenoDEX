// Copyright (c) DarkLightX/Dana Edwards. All rights reserved.

import { useState } from 'react';

// Tooltip component
export function Tooltip({ text, children }) {
    const [show, setShow] = useState(false);
    return (
        <span
            className="tooltip-container"
            onMouseEnter={() => setShow(true)}
            onMouseLeave={() => setShow(false)}
        >
            {children}
            {show && <span className="tooltip-text">{text}</span>}
        </span>
    );
}
