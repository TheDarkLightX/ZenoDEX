# ZenoDEX Full-System Paper Package

This directory is the public paper package for ZenoDEX.

## Which file to read

- `whitepaper.tex`
  - long-form whole-system paper
  - use this when reviewing the complete public architecture, assurance boundary,
    and end-state proof agenda
- `main.tex`
  - compact summary paper
  - use this when you want the short argument for the current architecture and
    RC1 claim boundary
- `appendix.tex`
  - audit companion
  - use this for claim-to-artifact mapping and the release-facing artifact ledger

## Package scope

The package is intentionally public-safe:

- it covers the full intended ZenoDEX architecture in detail
- it uses only public repo artifacts and public release documents as references
- it avoids non-public tooling details or private source pointers
- it keeps the RC1 public claim narrower than the full target architecture

## Build commands

### Short paper

```bash
cd docs/papers/zenodex-full-system
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

### Appendix

```bash
cd docs/papers/zenodex-full-system
pdflatex -interaction=nonstopmode -halt-on-error appendix.tex
pdflatex -interaction=nonstopmode -halt-on-error appendix.tex
```

### Whitepaper

```bash
cd docs/papers/zenodex-full-system
pdflatex -interaction=nonstopmode -halt-on-error whitepaper.tex
pdflatex -interaction=nonstopmode -halt-on-error whitepaper.tex
```
