#!/usr/bin/env python3
"""Simple Tkinter GUI to run Tau specs with input lines."""
import os
import shutil
import subprocess
import tkinter as tk
from tkinter import filedialog, messagebox
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def find_tau_bin() -> str:
    candidates = [
        ROOT / "external" / "tau-lang" / "build-Release" / "tau",
        ROOT / "external" / "tau-lang" / "build-Debug" / "tau",
        ROOT / "external" / "tau-nightly" / "usr" / "bin" / "tau",
    ]
    for c in candidates:
        if c.exists() and os.access(c, os.X_OK):
            return str(c)
    tau = shutil.which("tau")
    return tau or ""


def run_spec(tau_bin: str, spec_path: str, inputs: str) -> str:
    if not tau_bin:
        return "ERROR: Tau binary not found. Build it in external/tau-lang/build-Release."
    if not spec_path:
        return "ERROR: Spec file not set."

    input_lines = [line.strip() for line in inputs.splitlines() if line.strip() != ""]
    input_lines.append("q")

    try:
        result = subprocess.run(
            [tau_bin, spec_path, "--charvar", "false", "-x"],
            input="\n".join(input_lines),
            text=True,
            capture_output=True,
            cwd=str(ROOT),
            timeout=30,
        )
    except subprocess.TimeoutExpired:
        return "ERROR: Tau run timed out after 30s."

    out = result.stdout.strip()
    err = result.stderr.strip()
    if err:
        return out + "\n\n[stderr]\n" + err
    return out


class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Tau Spec Runner")
        self.geometry("900x700")

        self.tau_bin_var = tk.StringVar(value=find_tau_bin())
        self.spec_var = tk.StringVar(value="")

        self._build_ui()

    def _build_ui(self):
        top = tk.Frame(self)
        top.pack(fill=tk.X, padx=10, pady=8)

        tk.Label(top, text="Tau binary").grid(row=0, column=0, sticky="w")
        tk.Entry(top, textvariable=self.tau_bin_var, width=80).grid(row=0, column=1, padx=6)
        tk.Button(top, text="Browse", command=self._browse_tau).grid(row=0, column=2)

        tk.Label(top, text="Spec file").grid(row=1, column=0, sticky="w")
        tk.Entry(top, textvariable=self.spec_var, width=80).grid(row=1, column=1, padx=6)
        tk.Button(top, text="Browse", command=self._browse_spec).grid(row=1, column=2)

        mid = tk.Frame(self)
        mid.pack(fill=tk.BOTH, expand=True, padx=10, pady=8)

        tk.Label(mid, text="Input lines (one per line, order matters)").pack(anchor="w")
        self.input_text = tk.Text(mid, height=12)
        self.input_text.pack(fill=tk.BOTH, expand=True)

        tk.Button(self, text="Run Spec", command=self._run).pack(pady=6)

        bot = tk.Frame(self)
        bot.pack(fill=tk.BOTH, expand=True, padx=10, pady=8)
        tk.Label(bot, text="Output").pack(anchor="w")
        self.output_text = tk.Text(bot, height=18)
        self.output_text.pack(fill=tk.BOTH, expand=True)

    def _browse_tau(self):
        path = filedialog.askopenfilename(title="Select Tau binary")
        if path:
            self.tau_bin_var.set(path)

    def _browse_spec(self):
        path = filedialog.askopenfilename(title="Select Tau spec", filetypes=[("Tau spec", "*.tau")])
        if path:
            self.spec_var.set(path)

    def _run(self):
        out = run_spec(self.tau_bin_var.get(), self.spec_var.get(), self.input_text.get("1.0", tk.END))
        self.output_text.delete("1.0", tk.END)
        self.output_text.insert(tk.END, out)


if __name__ == "__main__":
    try:
        App().mainloop()
    except Exception as exc:
        messagebox.showerror("Error", str(exc))
