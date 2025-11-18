# Verification Analysis Report

## Executive Summary

- **Total code blocks**: 266
- **Successfully compiled**: 131 ✓
- **Failed (iverilog limitations)**: 32 ⚠️
- **Failed (actual errors)**: 92 ❌
- **Skipped (incomplete)**: 11

## Key Findings

### iverilog Limitations

The following advanced SystemVerilog features are NOT supported by iverilog 12.0:

- **Inside**: 15 instances
- **Unpacked Struct**: 7 instances
- **Dynamic Array**: 4 instances
- **Break**: 2 instances
- **Uvm**: 2 instances
- **String Methods**: 1 instances
- **Lifetime**: 1 instances

### Actual Code Issues

These failures indicate potential code problems:

- **syntax_error**: 27 instances
- **syntax_invalid_item**: 25 instances
- **other_error**: 18 instances
- **syntax_increment_operator**: 17 instances
- **missing_dependency**: 4 instances
- **type_mismatch**: 1 instances

## Recommendations

1. **iverilog limitations** - These are expected and not code errors. Consider:
   - Using a commercial simulator (VCS, Questa, Xcelium) for full SystemVerilog support
   - Using Verilator for better SystemVerilog support (still has limitations)
   - Marking these examples as "Advanced" features

2. **Syntax errors** - Review and fix:
   - Increment/decrement operators (++/--) usage
   - Array indexing and slicing syntax
   - Missing semicolons or malformed statements

3. **Missing dependencies** - Some modules reference undefined modules
   - Add the required module definitions
   - Or mark these as partial examples

