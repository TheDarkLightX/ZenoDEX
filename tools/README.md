# Tools

## Zeno Burn Demo (HTML)

Open in a browser:
```
open tools/zeno_burn_demo.html
```

This visualizes the Zeno-style burn: each step burns a fixed percentage of remaining supply.

## Tau Spec Runner (GUI)

Run:
```
python3 tools/tau_spec_runner_gui.py
```

- Choose a Tau binary (auto-detected if built in `external/tau-lang/build-Release/tau`).
- Choose a `.tau` spec.
- Paste input values line-by-line and run.

Note: Specs with long runs may take time; the GUI uses a 30s timeout.
