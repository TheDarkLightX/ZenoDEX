# Testing Tau Language Specifications

## Overview

This directory contains tests for TauSwap's Tau Language specifications. The specs must be validated to ensure they:
1. Parse correctly (valid syntax)
2. Are satisfiable (not contradictory)
3. Encode the intended properties correctly

## Prerequisites

1. **Install Tau Language**:
   ```bash
   # Option 1: Download pre-built binary
   # See: https://github.com/IDNI/tau-lang/releases
   
   # Option 2: Build from source
   cd external/tau-lang
   ./release.sh
   ```

2. **Verify installation**:
   ```bash
   tau --version
   ```

## Running Tests

```bash
cd tests/tau
chmod +x test_tau_specs.sh
./test_tau_specs.sh
```

## Test Structure

### Syntax Validation
- Each `.tau` file is parsed to check for syntax errors
- Stream declarations are validated
- Type definitions are checked

### Property Validation
- Invariants are checked for satisfiability
- Temporal properties are validated
- Constraint consistency is verified

## Current Status

⚠️ **Note**: The Tau specs are currently being rewritten to use actual Tau Language syntax. The original specs were pseudo-code comments.

## Next Steps

1. Complete rewrite of all specs in valid Tau syntax
2. Add property-based tests
3. Create test vectors for each spec
4. Integrate with CI/CD pipeline

## References

- [Tau Language Documentation](https://github.com/IDNI/tau-lang)
- [Tau Language README](https://github.com/IDNI/tau-lang/blob/main/README.md)

